import LambdaSigil.PublicFrameSecurity
import LambdaSigil.PublicLocalSecurity
import LambdaSigil.PublicReleaseSynchronization
import LambdaSigil.V9OccurrenceKernelSecurity
import LambdaSigil.DecodedOccurrencePrefix
import Mathlib.Data.Nat.Find

/-!
# Raw activation paths and verifier-derived region convergence

The decoded control graph is intraprocedural: a call has one summary edge to its real caller
continuation, while the raw machine pushes a frame and executes the callee.  This file supplies
the operational bridge without flattening recursive invocations or trusting a merge operand.

An activation is identified by its suspended caller stack.  While callees are active, the
outermost frame above that stack anchors every raw state at the original call instruction.  Thus
callee execution is genuine raw execution but stutters in the caller graph; the successful
return step takes the checked call-to-continuation edge.  The construction is proof-only and
does not change `step`, substitute events, or assume a common execution bound.
-/

namespace LambdaSigil.Combined.Semantic.PublicRegionConvergence

open OccurrenceRegions OccurrenceRegionSecurity OccurrenceTransfer
open OccurrenceTransferSecurity DecodedOccurrence DecodedOccurrenceSecurity
open OccurrenceInvocation
open V9.OccurrenceDataflowInvocation V9.OccurrenceKernel
open V9.OccurrenceKernelSecurity
open PublicRegionSecurity PublicFrameSecurity
open PublicReleaseSynchronization
open V9.PublicLocalSecurity

/-- A finite raw state trace.  It contains the starting state and the state after every step. -/
def rawStateTrace (p : SemanticProgram) : Nat → State → List State
  | 0, state => [state]
  | fuel + 1, state => state :: rawStateTrace p fuel (step p state).state

@[simp] theorem rawStateTrace_zero (p : SemanticProgram) (state : State) :
    rawStateTrace p 0 state = [state] := rfl

@[simp] theorem rawStateTrace_succ (p : SemanticProgram) (fuel : Nat) (state : State) :
    rawStateTrace p (fuel + 1) state = state :: rawStateTrace p fuel (step p state).state := rfl

theorem rawStateTrace_length (p : SemanticProgram) (fuel : Nat) (state : State) :
    (rawStateTrace p fuel state).length = fuel + 1 := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih => simp [rawStateTrace, ih]

theorem rawStateTrace_get (p : SemanticProgram) (fuel elapsed : Nat) (state : State)
    (helapsed : elapsed ≤ fuel) :
    (rawStateTrace p fuel state)[elapsed]? = some (runPrefix p elapsed state).state := by
  induction elapsed generalizing fuel state with
  | zero => cases fuel <;> rfl
  | succ elapsed ih =>
      cases fuel with
      | zero => omega
      | succ fuel =>
          simp only [rawStateTrace_succ, List.getElem?_cons_succ]
          rw [ih fuel (step p state).state (by omega)]
          simp [runPrefix]

/-- A path with explicit raw stuttering.  Repeated vertices are retained, so recursive or direct
    callee steps can be audited instead of disappearing from the execution witness. -/
inductive StutteringControlPath (graph : ControlGraph) : Nat → Nat → List Nat → Prop
  | single (node : Nat) : StutteringControlPath graph node node [node]
  | stay {source exit : Nat} {tail : List Nat}
      (rest : StutteringControlPath graph source exit tail) :
      StutteringControlPath graph source exit (source :: tail)
  | next {source target exit : Nat} {tail : List Nat}
      (bound : source < graph.size)
      (edge : target ∈ graph.successors.getD source [])
      (rest : StutteringControlPath graph target exit tail) :
      StutteringControlPath graph source exit (source :: tail)

/-- Erasing only raw stutters produces an ordinary decoded control path.  The returned trace is
    a subsequence of the raw anchor trace, so every reported continuation has a real occurrence. -/
theorem StutteringControlPath.toControlPath {graph : ControlGraph} {source exit : Nat}
    {trace : List Nat} (hpath : StutteringControlPath graph source exit trace) :
    ∃ compressed, ControlPath graph source exit compressed ∧
      compressed.Sublist trace := by
  induction hpath with
  | single node => exact ⟨[node], .single node, List.Sublist.refl _⟩
  | @stay source exit tail rest ih =>
      obtain ⟨compressed, hcompressed, hsublist⟩ := ih
      exact ⟨compressed, hcompressed, hsublist.cons _⟩
  | @next source target exit tail hbound hedge rest ih =>
      obtain ⟨compressed, hcompressed, hsublist⟩ := ih
      exact ⟨source :: compressed, .next hbound hedge hcompressed, hsublist.cons_cons source⟩

theorem StutteringControlPath.start_mem {graph : ControlGraph} {source exit : Nat}
    {trace : List Nat} (hpath : StutteringControlPath graph source exit trace) :
    source ∈ trace := by
  cases hpath <;> simp

theorem controlPath_start_mem {graph : ControlGraph} {source exit : Nat}
    {trace : List Nat} (hpath : ControlPath graph source exit trace) : source ∈ trace := by
  cases hpath <;> simp

/-- Compression removes only repeated stutters.  It therefore preserves the set of anchor
    vertices in both directions, not merely as a sublist. -/
theorem StutteringControlPath.toControlPath_cover {graph : ControlGraph} {source exit : Nat}
    {trace : List Nat} (hpath : StutteringControlPath graph source exit trace) :
    ∃ compressed, ControlPath graph source exit compressed ∧
      compressed.Sublist trace ∧ ∀ node, node ∈ trace → node ∈ compressed := by
  induction hpath with
  | single node =>
      exact ⟨[node], .single node, List.Sublist.refl _, by simp⟩
  | @stay source exit tail rest ih =>
      obtain ⟨compressed, hcompressed, hsublist, hcover⟩ := ih
      refine ⟨compressed, hcompressed, hsublist.cons _, ?_⟩
      intro node hmember
      simp only [List.mem_cons] at hmember
      rcases hmember with heq | hmember
      · exact heq ▸ controlPath_start_mem hcompressed
      · exact hcover node hmember
  | @next source target exit tail hbound hedge rest ih =>
      obtain ⟨compressed, hcompressed, hsublist, hcover⟩ := ih
      refine ⟨source :: compressed, .next hbound hedge hcompressed,
        hsublist.cons_cons source, ?_⟩
      intro node hmember
      simp only [List.mem_cons] at hmember ⊢
      rcases hmember with rfl | hmember
      · exact Or.inl rfl
      · exact Or.inr (hcover node hmember)

/-- The current activation is named by its exact suspended caller stack.  Descendant states use
    the outermost frame above that stack; its `returnPc - 1` is the real caller call site. -/
inductive ActivationAnchor (spine : List CallFrame) : Nat → State → Prop
  | current {state : State} (stack : state.callStack = spine) :
      ActivationAnchor spine state.pc state
  | descendant {state : State} (inner : List CallFrame) (outer : CallFrame)
      (stack : state.callStack = inner ++ outer :: spine) :
      ActivationAnchor spine (outer.returnPc - 1) state

theorem ActivationAnchor.exists_of_suffix {spine stack : List CallFrame} {state : State}
    (hstack : state.callStack = stack ++ spine) : ∃ node, ActivationAnchor spine node state := by
  rcases List.eq_nil_or_concat stack with hnil | ⟨inner, outer, hconcat⟩
  · subst stack
    exact ⟨state.pc, .current (by simpa using hstack)⟩
  · subst stack
    refine ⟨outer.returnPc - 1, .descendant inner outer ?_⟩
    simpa [List.append_assoc] using hstack

theorem ActivationAnchor.current_injective {spine : List CallFrame} {left : Nat}
    {state : State} (hleft : ActivationAnchor spine left state)
    (hright : state.callStack = spine) : left = state.pc := by
  cases hleft with
  | current _ => rfl
  | descendant inner outer hstack =>
      have hlength := congrArg List.length (hstack.symm.trans hright)
      simp at hlength
      omega

theorem ActivationAnchor.unique {spine : List CallFrame} {left right : Nat} {state : State}
    (hleft : ActivationAnchor spine left state) (hright : ActivationAnchor spine right state) :
    left = right := by
  cases hleft with
  | current hleftStack =>
      exact (hright.current_injective hleftStack).symm
  | descendant leftInner leftOuter hleftStack =>
      cases hright with
      | current hrightStack =>
          have hlength := congrArg List.length (hleftStack.symm.trans hrightStack)
          simp at hlength
          omega
      | descendant rightInner rightOuter hrightStack =>
          have hpadded : (leftInner ++ [leftOuter]) ++ spine =
              (rightInner ++ [rightOuter]) ++ spine := by
            simpa [List.append_assoc] using hleftStack.symm.trans hrightStack
          have hprefix := List.append_cancel_right hpadded
          have hlast := congrArg List.getLast? hprefix
          simp only [List.getLast?_concat, Option.some.injEq] at hlast
          simp [hlast]

/-- A raw step either remains at the same caller anchor or takes one actual decoded edge.  This
    relation is the local target consumed by the finite-trace composition below. -/
def AnchoredStep (p : SemanticProgram) (spine : List CallFrame)
    (left right : State) : Prop :=
  ∃ source target,
    ActivationAnchor spine source left ∧ ActivationAnchor spine target right ∧
      (source = target ∨
        source < (decodedControlGraph p).size ∧
          target ∈ (decodedControlGraph p).successors.getD source [])

/-- Complete live stack effect of one raw instruction.  The return case includes the exact saved
    continuation; the push case includes the exact caller pc used to construct the frame. -/
inductive RawStackTransition (instruction : Instruction) (state next : State) : Prop
  | same (stack : next.callStack = state.callStack)
      (notCall : instruction.op ≠ .call) (notClosure : instruction.op ≠ .closure)
      (notReturn : instruction.op ≠ .output) : RawStackTransition instruction state next
  | push (frame : CallFrame)
      (stack : next.callStack = frame :: state.callStack)
      (returnPc : frame.returnPc = state.pc + 1)
      (operation : instruction.op = .call ∨ instruction.op = .closure) :
      RawStackTransition instruction state next
  | pop (frame : CallFrame) (rest : List CallFrame)
      (before : state.callStack = frame :: rest)
      (after : next.callStack = rest)
      (continuation : next.pc = frame.returnPc)
      (operation : instruction.op = .output) : RawStackTransition instruction state next

/-- The current raw stack is inside the activation whose suspended caller stack is `spine`.
    The prefix is the (possibly empty) stack of recursive or nested callees. -/
def ActivationLive (spine : List CallFrame) (state : State) : Prop :=
  ∃ privatePrefix, state.callStack = privatePrefix ++ spine

@[simp] theorem activationLive_current (spine : List CallFrame) (state : State)
    (hstack : state.callStack = spine) : ActivationLive spine state :=
  ⟨[], by simpa using hstack⟩

/-- LIFO stack transitions preserve an activation suffix unless the step is precisely the output
    that pops that activation's own outer frame.  No numeric stack-depth approximation is used. -/
theorem RawStackTransition.activation_live_or_exit {instruction : Instruction}
    {state next : State} {spine : List CallFrame}
    (htransition : RawStackTransition instruction state next)
    (hlive : ActivationLive spine state) :
    ActivationLive spine next ∨
      ∃ frame rest, spine = frame :: rest ∧ state.callStack = spine ∧
        next.callStack = rest ∧ instruction.op = .output := by
  obtain ⟨privatePrefix, hstack⟩ := hlive
  cases htransition with
  | same hsame _ _ _ =>
      exact Or.inl ⟨privatePrefix, hsame.trans hstack⟩
  | push frame hpush _ _ =>
      exact Or.inl ⟨frame :: privatePrefix, by simp [hpush, hstack]⟩
  | pop frame rest hbefore hafter _ hop =>
      cases privatePrefix with
      | nil =>
          have hspine : spine = frame :: rest := by
            simpa using hstack.symm.trans hbefore
          exact Or.inr ⟨frame, rest, hspine, by simpa [hspine] using hbefore,
            hafter, hop⟩
      | cons privateHead privateTail =>
          have hcons : frame :: rest = privateHead :: (privateTail ++ spine) := by
            simpa using hbefore.symm.trans hstack
          have hrest : rest = privateTail ++ spine := List.cons.inj hcons |>.2
          exact Or.inl ⟨privateTail, hafter.trans hrest⟩

/-- A live-to-live raw step has exactly one of the three stack effects above.  Failed call,
    closure, and return checks trap and therefore cannot inhabit this theorem. -/
theorem live_step_stack_transition {p : SemanticProgram} {state : State}
    {instruction : Instruction}
    (hlookup : p.instructions[state.pc]? = some instruction)
    (hlive : state.halted = false) (hnotTrapped : state.trapped = false)
    (hnextLive : (step p state).state.halted = false)
    (hnextNotTrapped : (step p state).state.trapped = false) :
    RawStackTransition instruction state (step p state).state := by
  simp only [step, hlive, hnotTrapped, Bool.false_or, Bool.false_eq_true, if_false,
    hlookup] at hnextLive hnextNotTrapped ⊢
  cases hop : instruction.op <;> simp only [hop] at hnextLive hnextNotTrapped ⊢
  case call =>
    unfold callStep at hnextLive hnextNotTrapped ⊢
    split
    · simp_all
    · rename_i callee hcallee
      dsimp only
      split
      · simp_all
      · exact .push
          { returnPc := state.pc + 1, destination := instruction.destination,
            calleeId := callee.id, returnLabel := callee.returnLabel,
            savedParameters := saveValues state callee.parameterCells.toList }
          (by simp) rfl (Or.inl hop)
  case closure =>
    unfold callStep at hnextLive hnextNotTrapped ⊢
    split
    · simp_all
    · rename_i callee hcallee
      dsimp only
      split
      · simp_all
      · exact .push
          { returnPc := state.pc + 1, destination := instruction.destination,
            calleeId := callee.id, returnLabel := callee.returnLabel,
            savedParameters := saveValues state callee.parameterCells.toList }
          (by simp) rfl (Or.inr hop)
  case output =>
    cases hstack : state.callStack with
    | nil => simp_all
    | cons frame rest =>
        simp only [hstack] at hnextLive hnextNotTrapped ⊢
        split
        · simp_all
        · exact .pop frame rest hstack (by simp) (by simp) hop
  case actorBoundary =>
    apply RawStackTransition.same
    by_cases hdestination : instruction.destination = 0 <;>
      simp [hdestination, advanceExternal]
    all_goals simp [hop]
  all_goals
    exact .same (by simp [ordinaryStep, advanceExternal]) (by simp [hop])
      (by simp [hop]) (by simp [hop])

/-- An ordinary live step at the current activation takes the exact decoded edge.  Calls,
    closures, and returns are intentionally excluded here; their balanced cases are below. -/
theorem current_noncall_step_is_anchored {p : SemanticProgram} {root : UInt32}
    {spine : List CallFrame} {state : State} {instruction : Instruction}
    (hactive : ActiveState p root state) (hstack : state.callStack = spine)
    (hlookup : p.instructions[state.pc]? = some instruction)
    (hcall : instruction.op ≠ .call) (hclosure : instruction.op ≠ .closure)
    (hreturn : instruction.op ≠ .output)
    (hnextActive : ActiveState p root (step p state).state) :
    AnchoredStep p spine state (step p state).state := by
  have hedge := raw_noncall_step_follows_cfg hlookup hactive.notHalted hactive.notTrapped
    hnextActive.notHalted hnextActive.notTrapped hcall hclosure hreturn
  refine ⟨state.pc, (step p state).state.pc, .current hstack, ?_, Or.inr ⟨?_, ?_⟩⟩
  · exact .current (by
      have hsame : (step p state).state.callStack = state.callStack := by
        simp only [step, hactive.notHalted, hactive.notTrapped, Bool.false_or,
          Bool.false_eq_true, if_false, hlookup]
        cases hop : instruction.op <;> simp_all [ordinaryStep, advanceExternal]
        case actorBoundary => split <;> simp_all
      exact hsame.trans hstack)
  · have hpc : state.pc < p.instructions.size := (Array.getElem?_eq_some_iff.mp hlookup).1
    simp [ControlGraph.size, decodedControlGraph]
    omega
  · have hpc : state.pc < p.instructions.size := (Array.getElem?_eq_some_iff.mp hlookup).1
    have hinstruction : p.instructions[state.pc] = instruction :=
      (Array.getElem?_eq_some_iff.mp hlookup).2
    rw [decodedControlGraph_instruction_edges p state.pc hpc, hinstruction]
    exact hedge

/-- Successful direct, closure, and recursive entry is a raw step but a caller-graph stutter.
    The actual callee and argument payloads may differ between related runs. -/
theorem current_call_entry_is_anchored {p : SemanticProgram} {spine : List CallFrame}
    {state : State} {instruction : Instruction} {callee : Function} {arguments : List Value}
    (hstack : state.callStack = spine)
    (hstep : (step p state).state = privateCallEntry p state instruction callee arguments)
    (hreturnPc : (privateCallFrame state instruction callee).returnPc = state.pc + 1) :
    AnchoredStep p spine state (step p state).state := by
  refine ⟨state.pc, state.pc, .current hstack, ?_, Or.inl rfl⟩
  rw [hstep]
  have hanchor : ActivationAnchor spine
      ((privateCallFrame state instruction callee).returnPc - 1)
      (privateCallEntry p state instruction callee arguments) :=
    .descendant [] (privateCallFrame state instruction callee) (by simp [hstack])
  simpa [hreturnPc] using hanchor

/-- Every descendant step that retains the same outer frame is a caller-graph stutter.  This
    covers all ordinary callee instructions, nested calls, and returns from deeper recursion. -/
theorem descendant_step_is_anchored {p : SemanticProgram} {spine : List CallFrame}
    {state : State} {inner nextInner : List CallFrame} {outer : CallFrame}
    (hstack : state.callStack = inner ++ outer :: spine)
    (hnextStack : (step p state).state.callStack = nextInner ++ outer :: spine) :
    AnchoredStep p spine state (step p state).state := by
  exact ⟨outer.returnPc - 1, outer.returnPc - 1,
    .descendant inner outer hstack, .descendant nextInner outer hnextStack, Or.inl rfl⟩

/-- Returning through the outermost private frame takes the call summary edge stored in that
    genuine frame. `FrameDeclarationCoherent` ties `returnPc - 1` to an actual decoded call or
    closure and ties `returnPc` to its same-function continuation. -/
theorem outer_return_takes_summary_edge {p : SemanticProgram} {root : UInt32}
    {spine : List CallFrame} {state : State} {outer : CallFrame}
    (hstack : state.callStack = outer :: spine)
    (hnextStack : (step p state).state.callStack = spine)
    (hnextPc : (step p state).state.pc = outer.returnPc)
    (hframe : FrameDeclarationCoherent p (activeFunctionId root spine) outer) :
    AnchoredStep p spine state (step p state).state := by
  obtain ⟨caller, callee, call, continuation, hcaller, hcallee, hpositive, hcall,
    hcallFunction, hcallOp, hdestination, hdirect, hcontinuation,
    hcontinuationFunction, hreturnLabel, hsaved⟩ := hframe
  have hsourceBound : outer.returnPc - 1 < p.instructions.size :=
    (Array.getElem?_eq_some_iff.mp hcall).1
  have hgraphBound : outer.returnPc - 1 < (decodedControlGraph p).size := by
    simp [ControlGraph.size, decodedControlGraph]
    omega
  have hcallInstruction : p.instructions[outer.returnPc - 1] = call :=
    (Array.getElem?_eq_some_iff.mp hcall).2
  have hedge : outer.returnPc ∈
      (decodedControlGraph p).successors.getD (outer.returnPc - 1) [] := by
    rw [decodedControlGraph_instruction_edges p (outer.returnPc - 1) hsourceBound,
      hcallInstruction]
    rcases hcallOp with hop | hop <;> simp [instructionSuccessors, hop] <;> omega
  refine ⟨outer.returnPc - 1, outer.returnPc,
    .descendant [] outer (by simpa using hstack), ?_, Or.inr ⟨hgraphBound, hedge⟩⟩
  simpa [hnextPc] using (ActivationAnchor.current (spine := spine) hnextStack)

/-- Complete balanced one-step bridge.  The two `ActiveState` witnesses come from adjacent strict
    prefixes of one `SuccessfulExecution`; the supplied anchors identify the same activation.
    Direct calls, closure calls, and recursion stutter at their outer call site, while the pop of
    that outer frame takes its genuine decoded summary edge. -/
theorem live_step_is_anchored {p : SemanticProgram} {root : UInt32}
    {spine : List CallFrame} {state : State} {source target : Nat}
    (hactive : ActiveState p root state)
    (hnextActive : ActiveState p root (step p state).state)
    (hsource : ActivationAnchor spine source state)
    (htarget : ActivationAnchor spine target (step p state).state) :
    AnchoredStep p spine state (step p state).state := by
  obtain ⟨instruction, hlookup, _⟩ := hactive.currentInstruction
  have htransition := live_step_stack_transition hlookup hactive.notHalted hactive.notTrapped
    hnextActive.notHalted hnextActive.notTrapped
  refine ⟨source, target, hsource, htarget, ?_⟩
  cases htransition with
  | same hstack hnotCall hnotClosure hnotReturn =>
      cases hsource with
      | current hcurrent =>
          have hnextStack : (step p state).state.callStack = spine := hstack.trans hcurrent
          have htargetEq : target = (step p state).state.pc :=
            htarget.current_injective hnextStack
          subst target
          have hedge := raw_noncall_step_follows_cfg hlookup hactive.notHalted
            hactive.notTrapped hnextActive.notHalted hnextActive.notTrapped
            hnotCall hnotClosure hnotReturn
          right
          constructor
          · have hpc := (Array.getElem?_eq_some_iff.mp hlookup).1
            simp [ControlGraph.size, decodedControlGraph]
            omega
          · have hpc := (Array.getElem?_eq_some_iff.mp hlookup).1
            have hinstruction : p.instructions[state.pc] = instruction :=
              (Array.getElem?_eq_some_iff.mp hlookup).2
            rw [decodedControlGraph_instruction_edges p state.pc hpc, hinstruction]
            exact hedge
      | descendant inner outer hdescendant =>
          left
          have hcanonical : ActivationAnchor spine (outer.returnPc - 1) (step p state).state :=
            .descendant inner outer (hstack.trans hdescendant)
          exact (htarget.unique hcanonical).symm
  | push frame hstack hreturnPc _ =>
      left
      cases hsource with
      | current hcurrent =>
          have hcanonical : ActivationAnchor spine (frame.returnPc - 1) (step p state).state :=
            .descendant [] frame (by simpa [hcurrent] using hstack)
          have htargetEq : target = frame.returnPc - 1 := htarget.unique hcanonical
          rw [htargetEq, hreturnPc]
          omega
      | descendant inner outer hdescendant =>
          have hcanonical : ActivationAnchor spine (outer.returnPc - 1) (step p state).state :=
            .descendant (frame :: inner) outer (by
              simpa [hdescendant, List.append_assoc] using hstack)
          exact (htarget.unique hcanonical).symm
  | pop frame rest hbefore hafter hcontinuation _ =>
      cases hsource with
      | current hcurrent =>
          exfalso
          cases htarget with
          | current htargetStack =>
              have hbeforeLength := congrArg List.length (hbefore.symm.trans hcurrent)
              have hafterLength := congrArg List.length (hafter.symm.trans htargetStack)
              simp at hbeforeLength hafterLength
              omega
          | descendant inner outer htargetStack =>
              have hbeforeLength := congrArg List.length (hbefore.symm.trans hcurrent)
              have hafterLength := congrArg List.length (hafter.symm.trans htargetStack)
              simp at hbeforeLength hafterLength
              omega
      | descendant inner outer hdescendant =>
          cases inner with
          | nil =>
              simp only [List.nil_append] at hdescendant
              have hcons : frame :: rest = outer :: spine := hbefore.symm.trans hdescendant
              have hframeEq : frame = outer := List.cons.inj hcons |>.1
              have hrestEq : rest = spine := List.cons.inj hcons |>.2
              have hnextStack : (step p state).state.callStack = spine :=
                hafter.trans hrestEq
              have hnextPc : (step p state).state.pc = outer.returnPc :=
                hcontinuation.trans (congrArg CallFrame.returnPc hframeEq)
              have hchain : FrameDeclarationCoherent p (activeFunctionId root spine) outer := by
                have hchainAll := hactive.frameChain
                rw [hdescendant] at hchainAll
                exact hchainAll.1
              have hsummarized := outer_return_takes_summary_edge (p := p) (root := root)
                hdescendant hnextStack hnextPc hchain
              obtain ⟨leftNode, rightNode, hleft, hright, hmovement⟩ := hsummarized
              have hleftCanonical : ActivationAnchor spine (outer.returnPc - 1) state :=
                .descendant [] outer hdescendant
              have hrightCanonical : ActivationAnchor spine outer.returnPc (step p state).state := by
                simpa [hnextPc] using (ActivationAnchor.current (spine := spine) hnextStack)
              have hleftEq : leftNode = outer.returnPc - 1 := hleft.unique hleftCanonical
              have hrightEq : rightNode = outer.returnPc := hright.unique hrightCanonical
              have htargetEq : target = outer.returnPc := htarget.unique hrightCanonical
              simpa [hleftEq, hrightEq, htargetEq] using hmovement
          | cons innerHead innerTail =>
              left
              have hcons : frame :: rest = innerHead :: innerTail ++ outer :: spine :=
                hbefore.symm.trans hdescendant
              have hrestEq : rest = innerTail ++ outer :: spine := List.cons.inj hcons |>.2
              have hcanonical : ActivationAnchor spine (outer.returnPc - 1)
                  (step p state).state :=
                .descendant innerTail outer (by simpa [hrestEq] using hafter)
              exact (htarget.unique hcanonical).symm

/-- Actual repeated raw stepping, indexed by its two endpoint anchors.  There is no trace or
    state substitution: every successor is definitionally `step p state`. -/
inductive AnchoredRawPath (p : SemanticProgram) (spine : List CallFrame) :
    Nat → State → Nat → State → Nat → List Nat → Prop
  | zero {state : State} {node : Nat} (anchor : ActivationAnchor spine node state) :
      AnchoredRawPath p spine 0 state node state node [node]
  | succ {fuel : Nat} {state finish : State} {source target exit : Nat} {tail : List Nat}
      (head : ActivationAnchor spine source state)
      (edge : ActivationAnchor spine target (step p state).state)
      (movement : source = target ∨
        source < (decodedControlGraph p).size ∧
          target ∈ (decodedControlGraph p).successors.getD source [])
      (rest : AnchoredRawPath p spine fuel (step p state).state target finish exit tail) :
      AnchoredRawPath p spine (fuel + 1) state source finish exit (source :: tail)

theorem AnchoredRawPath.toStutteringControlPath {p : SemanticProgram}
    {spine : List CallFrame} {fuel : Nat} {start finish : State} {source exit : Nat}
    {trace : List Nat} (hpath : AnchoredRawPath p spine fuel start source finish exit trace) :
    StutteringControlPath (decodedControlGraph p) source exit trace := by
  induction hpath with
  | zero anchor => exact .single _
  | @succ fuel state finish source target exit tail head edge movement rest ih =>
      rcases movement with heq | ⟨hbound, hedge⟩
      · subst target
        exact .stay ih
      · exact .next hbound hedge ih

theorem AnchoredRawPath.endAnchor {p : SemanticProgram} {spine : List CallFrame}
    {fuel : Nat} {start finish : State} {source exit : Nat} {trace : List Nat}
    (hpath : AnchoredRawPath p spine fuel start source finish exit trace) :
    ActivationAnchor spine exit finish := by
  induction hpath with
  | zero anchor => exact anchor
  | succ head edge movement rest ih => exact ih

@[simp] theorem AnchoredRawPath.trace_length {p : SemanticProgram}
    {spine : List CallFrame} {fuel : Nat} {start finish : State} {source exit : Nat}
    {trace : List Nat} (hpath : AnchoredRawPath p spine fuel start source finish exit trace) :
    trace.length = fuel + 1 := by
  induction hpath with
  | zero anchor => rfl
  | succ head edge movement rest ih => simp [ih]

/-- The anchor at list position `elapsed` belongs to the actual state reached after exactly that
    many raw steps.  This is the occurrence-preserving counterpart of path compression. -/
theorem AnchoredRawPath.get_anchor {p : SemanticProgram} {spine : List CallFrame}
    {fuel : Nat} {start finish : State} {source exit : Nat} {trace : List Nat}
    (hpath : AnchoredRawPath p spine fuel start source finish exit trace)
    (elapsed : Nat) (helapsed : elapsed < trace.length) :
    ActivationAnchor spine (trace.get ⟨elapsed, helapsed⟩)
      (runPrefix p elapsed start).state := by
  induction hpath generalizing elapsed with
  | @zero state node anchor =>
      have : elapsed = 0 := by simpa using helapsed
      subst elapsed
      have hget : [node].get ⟨0, helapsed⟩ = node := rfl
      simpa only [runPrefix, hget] using anchor
  | @succ fuel state finish source target exit tail head edge movement rest ih =>
      cases elapsed with
      | zero =>
          have hget : (source :: tail).get ⟨0, helapsed⟩ = source := rfl
          simpa only [runPrefix, hget] using head
      | succ elapsed =>
          have htail : elapsed < tail.length := by simpa using helapsed
          have hget : (source :: tail).get ⟨elapsed + 1, helapsed⟩ =
              tail.get ⟨elapsed, htail⟩ := rfl
          simpa only [runPrefix, hget] using ih elapsed htail

/-- Taking an exact raw prefix preserves the anchored execution witness.  This is what lets the
    verifier reason about an independently chosen first-hit index without replaying the machine. -/
theorem AnchoredRawPath.take {p : SemanticProgram} {spine : List CallFrame}
    {fuel : Nat} {start finish : State} {source exit : Nat} {trace : List Nat}
    (hpath : AnchoredRawPath p spine fuel start source finish exit trace)
    (elapsed : Nat) (helapsed : elapsed ≤ fuel) :
    ∃ target prefixTrace,
      AnchoredRawPath p spine elapsed start source
        (runPrefix p elapsed start).state target prefixTrace := by
  induction elapsed generalizing fuel start source finish exit trace with
  | zero => exact ⟨source, [source], .zero (by cases hpath <;> assumption)⟩
  | succ elapsed ih =>
      cases hpath with
      | zero anchor => omega
      | @succ fuel state finish source target exit tail head edge movement rest =>
          obtain ⟨prefixExit, prefixTrace, hprefix⟩ := ih rest (by omega)
          refine ⟨prefixExit, source :: prefixTrace, .succ head edge movement ?_⟩
          simpa only [runPrefix] using hprefix

/-- Any vertex retained by a control path has the exact remaining suffix to the same exit. -/
theorem controlPath_suffix_of_mem {graph : ControlGraph} {source exit node : Nat}
    {trace : List Nat} (hpath : ControlPath graph source exit trace) (hnode : node ∈ trace) :
    ∃ suffix, ControlPath graph node exit suffix := by
  induction hpath with
  | single current =>
      have hnodeEq : node = current := by simpa using hnode
      subst node
      exact ⟨[current], .single current⟩
  | @next current target exit tail hbound hedge rest ih =>
      simp only [List.mem_cons] at hnode
      rcases hnode with hnodeEq | hnodeTail
      · subst node
        exact ⟨current :: tail, .next hbound hedge rest⟩
      · exact ih hnodeTail

theorem successfulPath_suffix_of_mem {graph : ControlGraph} {source node : Nat}
    {trace : List Nat} (hpath : SuccessfulPath graph source trace) (hnode : node ∈ trace) :
    ∃ suffix, SuccessfulPath graph node suffix := by
  obtain ⟨exit, hexit, hcontrol⟩ := hpath
  obtain ⟨suffix, hsuffix⟩ := controlPath_suffix_of_mem hcontrol hnode
  exact ⟨suffix, exit, hexit, hsuffix⟩

/-- Escape-index well-formedness supplies the bound for the start of every successful path. -/
theorem checked_successful_path_start_bound {graph : ControlGraph} {index : EscapeIndex}
    (hindex : escapeIndexChecks graph index = true) {source : Nat} {trace : List Nat}
    (hpath : SuccessfulPath graph source trace) : source < graph.size := by
  have hchecks := hindex
  simp only [escapeIndexChecks, Bool.and_eq_true] at hchecks
  have hgraph := hchecks.1.1.1.1
  simp only [ControlGraph.wellFormedB, Bool.and_eq_true, List.all_eq_true,
    Array.all_eq_true, decide_eq_true_eq] at hgraph
  obtain ⟨exit, hexit, hcontrol⟩ := hpath
  cases hcontrol with
  | single => exact (hgraph.1 source hexit).1
  | next hbound hedge rest => exact hbound

private theorem exists_first_split {node : Nat} {trace : List Nat} (hmem : node ∈ trace) :
    ∃ before after, trace = before ++ node :: after ∧ node ∉ before := by
  induction trace with
  | nil => simp at hmem
  | cons head tail ih =>
      by_cases heq : node = head
      · subst head
        exact ⟨[], tail, by simp, by simp⟩
      · have htail : node ∈ tail := by simpa [heq] using hmem
        obtain ⟨before, after, hsplit, hbefore⟩ := ih htail
        exact ⟨head :: before, after, by simp [hsplit], by simp [heq, hbefore]⟩

/-- A member of the raw anchor trace has an earliest exact raw prefix.  The minimality clause is
    over real `runPrefix` states and exact activation anchors, not over a substituted CFG trace. -/
theorem AnchoredRawPath.first_anchor_hit {p : SemanticProgram} {spine : List CallFrame}
    {fuel : Nat} {start finish : State} {source exit node : Nat} {trace : List Nat}
    (hpath : AnchoredRawPath p spine fuel start source finish exit trace)
    (hmem : node ∈ trace) :
    ∃ elapsed, elapsed ≤ fuel ∧
      ActivationAnchor spine node (runPrefix p elapsed start).state ∧
      ∀ earlier, earlier < elapsed →
        ¬ ActivationAnchor spine node (runPrefix p earlier start).state := by
  obtain ⟨before, after, hsplit, hbefore⟩ := exists_first_split hmem
  let elapsed := before.length
  have helapsedTrace : elapsed < trace.length := by
    simp [elapsed, hsplit]
  have hnodeAt : trace.get ⟨elapsed, helapsedTrace⟩ = node := by
    simp [elapsed, hsplit]
  have helapsedFuel : elapsed ≤ fuel := by
    rw [hpath.trace_length] at helapsedTrace
    omega
  have hanchor := hpath.get_anchor elapsed helapsedTrace
  rw [hnodeAt] at hanchor
  refine ⟨elapsed, helapsedFuel, hanchor, ?_⟩
  intro earlier hearlier hearlierAnchor
  have hearlierTrace : earlier < trace.length := by
    rw [hpath.trace_length]
    omega
  have htraceAnchor := hpath.get_anchor earlier hearlierTrace
  have heq : node = trace.get ⟨earlier, hearlierTrace⟩ :=
    hearlierAnchor.unique htraceAnchor
  have hearlierBefore : earlier < before.length := by simpa [elapsed] using hearlier
  have hbeforeMember : before.get ⟨earlier, hearlierBefore⟩ ∈ before :=
    List.getElem_mem hearlierBefore
  have htraceValue : trace.get ⟨earlier, hearlierTrace⟩ =
      before.get ⟨earlier, hearlierBefore⟩ := by
    simp [hsplit, hearlierBefore]
  apply hbefore
  rw [heq, htraceValue]
  exact hbeforeMember

theorem append_control_edge {graph : ControlGraph} {source middle target : Nat}
    {trace : List Nat} (hpath : ControlPath graph source middle trace)
    (hbound : middle < graph.size) (hedge : target ∈ graph.successors.getD middle []) :
    ControlPath graph source target (trace ++ [target]) := by
  induction hpath with
  | single node => simpa using ControlPath.next hbound hedge (.single target)
  | @next source next middle tail hsource hnext rest ih =>
      simpa using ControlPath.next hsource hnext (ih hbound hedge)

/-- Pointwise anchored-step evidence along a raw prefix composes for that prefix's actual,
    independently chosen length. This is the bridge used after the stack-discipline cases. -/
theorem anchoredRawPath_of_runPrefix {p : SemanticProgram} {spine : List CallFrame}
    (fuel : Nat) (start : State) (startNode : Nat)
    (hstart : ActivationAnchor spine startNode start)
    (hsteps : ∀ elapsed, elapsed < fuel →
      AnchoredStep p spine (runPrefix p elapsed start).state
        (step p (runPrefix p elapsed start).state).state) :
    ∃ (finish : State) (exit : Nat) (trace : List Nat),
      finish = (runPrefix p fuel start).state ∧
        AnchoredRawPath p spine fuel start startNode finish exit trace := by
  induction fuel generalizing start startNode with
  | zero => exact ⟨start, startNode, [startNode], rfl, .zero hstart⟩
  | succ fuel ih =>
      obtain ⟨source, target, hsource, htarget, hmovement⟩ := hsteps 0 (by omega)
      have hsourceEq : source = startNode := hsource.unique hstart
      subst source
      have htailSteps : ∀ elapsed, elapsed < fuel →
          AnchoredStep p spine
            (runPrefix p elapsed (step p start).state).state
            (step p (runPrefix p elapsed (step p start).state).state).state := by
        intro elapsed helapsed
        have hrow := hsteps (elapsed + 1) (by omega)
        simpa [runPrefix] using hrow
      obtain ⟨finish, exit, tail, hfinish, htail⟩ :=
        ih (step p start).state target htarget htailSteps
      refine ⟨finish, exit, startNode :: tail, ?_, .succ hstart htarget hmovement htail⟩
      simpa [runPrefix] using hfinish

/-- Every composed anchored raw prefix yields an ordinary decoded path after erasing only
    callee stutters. -/
theorem anchoredRawPath_to_decoded_control_path {p : SemanticProgram}
    {spine : List CallFrame} {fuel : Nat} {start finish : State} {source exit : Nat}
    {trace : List Nat} (hpath : AnchoredRawPath p spine fuel start source finish exit trace) :
    ∃ compressed, ControlPath (decodedControlGraph p) source exit compressed ∧
      compressed.Sublist trace :=
  hpath.toStutteringControlPath.toControlPath

/-- Exact root-level successful execution produces a finite successful decoded path. Callee and
    recursive steps are retained as raw stutters at the outer call site, then erased only after
    their balanced return has taken the real summary edge.  The final top-level output or halt
    takes the root's synthetic return edge. -/
theorem successful_root_execution_has_successful_control_path {p : SemanticProgram}
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result)
    (hstartStack : start.callStack = [])
    (hrootPositive : 0 < root.toNat) (hrootBound : root.toNat ≤ p.functions.size) :
    ∃ trace, SuccessfulPath (decodedControlGraph p) start.pc trace := by
  have hpositive := hexecution.positive
  let prefixFuel := steps - 1
  have hprefixBound : prefixFuel < steps := by
    dsimp [prefixFuel]
    omega
  have hpointwise : ∀ elapsed, elapsed < prefixFuel →
      AnchoredStep p [] (runPrefix p elapsed start).state
        (step p (runPrefix p elapsed start).state).state := by
    intro elapsed helapsed
    have hleftActive := hexecution.reached_active (elapsed := elapsed) (by omega)
    have hrightActive := hexecution.reached_active (elapsed := elapsed + 1) (by omega)
    obtain ⟨leftNode, hleftAnchor⟩ := ActivationAnchor.exists_of_suffix
      (state := (runPrefix p elapsed start).state) (spine := [])
      (stack := (runPrefix p elapsed start).state.callStack) (by simp)
    obtain ⟨rightNode, hrightAnchor⟩ := ActivationAnchor.exists_of_suffix
      (state := (step p (runPrefix p elapsed start).state).state) (spine := [])
      (stack := (step p (runPrefix p elapsed start).state).state.callStack) (by simp)
    have hnextState := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add p elapsed 1 start)
    simp only [runPrefix] at hnextState
    have hrightActive'' : ActiveState p root
        (runPrefix p elapsed (step p start).state).state := by
      simpa only [runPrefix] using hrightActive
    have hrightActive' : ActiveState p root
        (step p (runPrefix p elapsed start).state).state := by
      rw [← hnextState]
      exact hrightActive''
    exact live_step_is_anchored hleftActive hrightActive' hleftAnchor hrightAnchor
  obtain ⟨finish, exit, anchors, hfinish, hrawPath⟩ :=
    anchoredRawPath_of_runPrefix prefixFuel start start.pc (.current hstartStack) hpointwise
  obtain ⟨compressed, hcontrol, _⟩ := anchoredRawPath_to_decoded_control_path hrawPath
  have hlastTop := hexecution.lastTopLevel
  dsimp only at hlastTop
  obtain ⟨hbeforeStack, last, hlastLookup, hlastOp⟩ := hlastTop
  have hfinishBefore : finish = (runPrefix p (steps - 1) start).state := by
    simpa [prefixFuel] using hfinish
  have hexitAnchor := hrawPath.endAnchor
  rw [hfinishBefore] at hexitAnchor
  have hexitEq : exit = (runPrefix p (steps - 1) start).state.pc :=
    hexitAnchor.current_injective hbeforeStack
  have hlastActive := hexecution.reached_active (elapsed := steps - 1) (by omega)
  obtain ⟨activeLast, hactiveLastLookup, hactiveLastFunction⟩ :=
    hlastActive.currentInstruction
  have hlastEq : activeLast = last := by
    rw [hlastLookup] at hactiveLastLookup
    exact Option.some.inj hactiveLastLookup.symm
  subst activeLast
  have hlastFunction : last.functionId = root := by
    simpa [hbeforeStack, activeFunctionId] using hactiveLastFunction
  have hlastBound := (Array.getElem?_eq_some_iff.mp hlastLookup).1
  have hgraphBound : (runPrefix p (steps - 1) start).state.pc <
      (decodedControlGraph p).size := by
    simp [ControlGraph.size, decodedControlGraph]
    omega
  have hreturnEdge : functionReturn p root ∈
      (decodedControlGraph p).successors.getD
        (runPrefix p (steps - 1) start).state.pc [] := by
    rw [decodedControlGraph_instruction_edges p _ hlastBound]
    have hlastGet : p.instructions[(runPrefix p (steps - 1) start).state.pc] = last :=
      (Array.getElem?_eq_some_iff.mp hlastLookup).2
    rw [hlastGet]
    rcases hlastOp with hop | hop <;>
      simp [instructionSuccessors, hop, hlastFunction]
  have hsuccessfulExit : functionReturn p root ∈
      (decodedControlGraph p).successfulExits := by
    simp only [decodedControlGraph, functionReturn]
    rw [List.mem_range'_1]
    omega
  refine ⟨compressed ++ [functionReturn p root], functionReturn p root,
    hsuccessfulExit, ?_⟩
  rw [hexitEq] at hcontrol
  exact append_control_edge hcontrol hgraphBound hreturnEdge

/-- The strengthened root witness retains the exact raw anchor trace as well as its compressed
    successful CFG path.  This is the data needed to recover an exact raw hit index later. -/
theorem successful_root_execution_control_witness {p : SemanticProgram}
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result)
    (hstartStack : start.callStack = [])
    (hrootPositive : 0 < root.toNat) (hrootBound : root.toNat ≤ p.functions.size) :
    ∃ finish exit anchors compressed,
      finish = (runPrefix p (steps - 1) start).state ∧
        AnchoredRawPath p [] (steps - 1) start start.pc finish exit anchors ∧
        ControlPath (decodedControlGraph p) start.pc exit compressed ∧
        compressed.Sublist anchors ∧
        (∀ node, node ∈ anchors → node ∈ compressed) ∧
        SuccessfulPath (decodedControlGraph p) start.pc
      (compressed ++ [functionReturn p root]) := by
  have hpositive := hexecution.positive
  let prefixFuel := steps - 1
  have hprefixBound : prefixFuel < steps := by
    dsimp [prefixFuel]
    omega
  have hpointwise : ∀ elapsed, elapsed < prefixFuel →
      AnchoredStep p [] (runPrefix p elapsed start).state
        (step p (runPrefix p elapsed start).state).state := by
    intro elapsed helapsed
    have hleftActive := hexecution.reached_active (elapsed := elapsed) (by omega)
    have hrightActive := hexecution.reached_active (elapsed := elapsed + 1) (by omega)
    obtain ⟨leftNode, hleftAnchor⟩ := ActivationAnchor.exists_of_suffix
      (state := (runPrefix p elapsed start).state) (spine := [])
      (stack := (runPrefix p elapsed start).state.callStack) (by simp)
    obtain ⟨rightNode, hrightAnchor⟩ := ActivationAnchor.exists_of_suffix
      (state := (step p (runPrefix p elapsed start).state).state) (spine := [])
      (stack := (step p (runPrefix p elapsed start).state).state.callStack) (by simp)
    have hnextState := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add p elapsed 1 start)
    simp only [runPrefix] at hnextState
    have hrightActive'' : ActiveState p root
        (runPrefix p elapsed (step p start).state).state := by
      simpa only [runPrefix] using hrightActive
    have hrightActive' : ActiveState p root
        (step p (runPrefix p elapsed start).state).state := by
      rw [← hnextState]
      exact hrightActive''
    exact live_step_is_anchored hleftActive hrightActive' hleftAnchor hrightAnchor
  obtain ⟨finish, exit, anchors, hfinish, hrawPath⟩ :=
    anchoredRawPath_of_runPrefix prefixFuel start start.pc (.current hstartStack) hpointwise
  obtain ⟨compressed, hcontrol, hsublist, hcover⟩ :=
    hrawPath.toStutteringControlPath.toControlPath_cover
  have hlastTop := hexecution.lastTopLevel
  dsimp only at hlastTop
  obtain ⟨hbeforeStack, last, hlastLookup, hlastOp⟩ := hlastTop
  have hfinishBefore : finish = (runPrefix p (steps - 1) start).state := by
    simpa [prefixFuel] using hfinish
  have hexitAnchor := hrawPath.endAnchor
  rw [hfinishBefore] at hexitAnchor
  have hexitEq : exit = (runPrefix p (steps - 1) start).state.pc :=
    hexitAnchor.current_injective hbeforeStack
  have hlastActive := hexecution.reached_active (elapsed := steps - 1) (by omega)
  obtain ⟨activeLast, hactiveLastLookup, hactiveLastFunction⟩ :=
    hlastActive.currentInstruction
  have hlastEq : activeLast = last := by
    rw [hlastLookup] at hactiveLastLookup
    exact Option.some.inj hactiveLastLookup.symm
  subst activeLast
  have hlastFunction : last.functionId = root := by
    simpa [hbeforeStack, activeFunctionId] using hactiveLastFunction
  have hlastBound := (Array.getElem?_eq_some_iff.mp hlastLookup).1
  have hgraphBound : (runPrefix p (steps - 1) start).state.pc <
      (decodedControlGraph p).size := by
    simp [ControlGraph.size, decodedControlGraph]
    omega
  have hreturnEdge : functionReturn p root ∈
      (decodedControlGraph p).successors.getD
        (runPrefix p (steps - 1) start).state.pc [] := by
    rw [decodedControlGraph_instruction_edges p _ hlastBound]
    have hlastGet : p.instructions[(runPrefix p (steps - 1) start).state.pc] = last :=
      (Array.getElem?_eq_some_iff.mp hlastLookup).2
    rw [hlastGet]
    rcases hlastOp with hop | hop <;>
      simp [instructionSuccessors, hop, hlastFunction]
  have hsuccessfulExit : functionReturn p root ∈
      (decodedControlGraph p).successfulExits := by
    simp only [decodedControlGraph, functionReturn]
    rw [List.mem_range'_1]
    omega
  have hsuccessful : SuccessfulPath (decodedControlGraph p) start.pc
      (compressed ++ [functionReturn p root]) := by
    refine ⟨functionReturn p root, hsuccessfulExit, ?_⟩
    have hcontrol' := hcontrol
    rw [hexitEq] at hcontrol'
    exact append_control_edge hcontrol' hgraphBound hreturnEdge
  exact ⟨finish, exit, anchors, compressed, hfinishBefore, hrawPath, hcontrol,
    hsublist, hcover, hsuccessful⟩

/-- Operational realization of an intraprocedural continuation.  Ordinary vertices are reached
    by an exact activation anchor.  A synthetic function-return vertex is reached by the live raw
    state poised to execute that activation's real output (or a top-level halt). -/
def ActivationContinuationAt (p : SemanticProgram) (root : UInt32)
    (spine : List CallFrame) (node : Nat) (state : State) : Prop :=
  ActivationAnchor spine node state ∨
    (node = functionReturn p (activeFunctionId root spine) ∧
      state.callStack = spine ∧
      ∃ instruction, p.instructions[state.pc]? = some instruction ∧
        instruction.functionId = activeFunctionId root spine ∧
        (instruction.op = .output ∨ (spine = [] ∧ instruction.op = .halt)))

theorem reachableFromRoot_runPrefix_state {p : SemanticProgram} {root : UInt32}
    {start : State} (hreachable : ReachableFromRoot p root start) (fuel : Nat) :
    ReachableFromRoot p root (runPrefix p fuel start).state := by
  induction fuel generalizing start with
  | zero => simpa only [runPrefix] using hreachable
  | succ fuel ih =>
      simpa only [runPrefix] using ih hreachable.step

/-- A successful whole-program execution starting inside a non-root activation must leave that
    activation at a first real raw step.  Before that step every stack has the original suspended
    caller stack as an exact suffix; the step itself executes the activation's decoded output.
    This is the finite, frame-aware measure used for arbitrary activation convergence. -/
theorem successful_execution_first_activation_exit {p : SemanticProgram} {root : UInt32}
    {steps : Nat} {start : State} {result : StepResult} {spine : List CallFrame}
    (hexecution : SuccessfulExecution p root steps start result)
    (hstartStack : start.callStack = spine) (hspine : spine ≠ []) :
    ∃ exitStep instruction,
      0 < exitStep ∧ exitStep < steps ∧
        (∀ elapsed, elapsed < exitStep →
          ActivationLive spine (runPrefix p elapsed start).state) ∧
        (runPrefix p (exitStep - 1) start).state.callStack = spine ∧
        p.instructions[(runPrefix p (exitStep - 1) start).state.pc]? = some instruction ∧
        instruction.functionId = activeFunctionId root spine ∧
        instruction.op = .output := by
  classical
  have hpositive := hexecution.positive
  have hlastStack := hexecution.lastTopLevel.1
  have hnotLastLive :
      ¬ ActivationLive spine (runPrefix p (steps - 1) start).state := by
    rintro ⟨privatePrefix, hprefix⟩
    rw [hlastStack] at hprefix
    have hlength := congrArg List.length hprefix
    simp only [List.length_nil, List.length_append] at hlength
    have hspineLength : spine.length = 0 := by omega
    exact hspine (List.eq_nil_of_length_eq_zero hspineLength)
  have hexists : ∃ elapsed, elapsed < steps ∧
      ¬ ActivationLive spine (runPrefix p elapsed start).state :=
    ⟨steps - 1, by omega, hnotLastLive⟩
  let exitStep := Nat.find hexists
  have hexitSpec := Nat.find_spec hexists
  have hexitBound : exitStep < steps := by simpa [exitStep] using hexitSpec.1
  have hexitNotLive :
      ¬ ActivationLive spine (runPrefix p exitStep start).state := by
    simpa [exitStep] using hexitSpec.2
  have hexitPositive : 0 < exitStep := by
    by_contra hzero
    have heq : exitStep = 0 := Nat.eq_zero_of_not_pos hzero
    rw [heq] at hexitNotLive
    exact hexitNotLive (activationLive_current spine start hstartStack)
  have hprefixLive : ∀ elapsed, elapsed < exitStep →
      ActivationLive spine (runPrefix p elapsed start).state := by
    intro elapsed helapsed
    by_contra hnot
    exact Nat.find_min hexists helapsed ⟨by omega, hnot⟩
  let before := (runPrefix p (exitStep - 1) start).state
  have hbeforeLive : ActivationLive spine before := by
    exact hprefixLive (exitStep - 1) (by omega)
  have hbeforeActive := hexecution.reached_active (elapsed := exitStep - 1) (by omega)
  have hnextActiveRaw := hexecution.reached_active (elapsed := exitStep) hexitBound
  have hnextState : (runPrefix p exitStep start).state = (step p before).state := by
    have hadd := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add p (exitStep - 1) 1 start)
    have hsum : exitStep - 1 + 1 = exitStep := by omega
    rw [hsum] at hadd
    simpa only [runPrefix, before] using hadd
  have hnextActive : ActiveState p root (step p before).state := by
    rw [← hnextState]
    exact hnextActiveRaw
  obtain ⟨instruction, hlookup, hfunction⟩ := hbeforeActive.currentInstruction
  have htransition := live_step_stack_transition hlookup hbeforeActive.notHalted
    hbeforeActive.notTrapped hnextActive.notHalted hnextActive.notTrapped
  rcases htransition.activation_live_or_exit hbeforeLive with hstill | hexit
  · exfalso
    apply hexitNotLive
    rw [hnextState]
    exact hstill
  · obtain ⟨frame, rest, _, hbeforeStack, _, hop⟩ := hexit
    refine ⟨exitStep, instruction, hexitPositive, hexitBound, hprefixLive,
      ?_, hlookup, ?_, hop⟩
    · simpa [before] using hbeforeStack
    · simpa [hbeforeStack, before, activeFunctionId] using hfunction

/-- A successful suffix beginning in an arbitrary non-root activation yields that activation's
    exact successful decoded path.  Nested direct/closure calls and recursion remain in the raw
    anchor trace as stutters; the activation's own output is the only synthetic-return edge. -/
theorem successful_nonroot_activation_control_witness {p : SemanticProgram}
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hexecution : SuccessfulExecution p root steps start result)
    (hstartStack : start.callStack = spine) (hspine : spine ≠ [])
    (hactivePositive : 0 < (activeFunctionId root spine).toNat)
    (hactiveBound : (activeFunctionId root spine).toNat ≤ p.functions.size) :
    ∃ exitStep finish exit anchors compressed,
      0 < exitStep ∧ exitStep < steps ∧
        finish = (runPrefix p (exitStep - 1) start).state ∧
        AnchoredRawPath p spine (exitStep - 1) start start.pc finish exit anchors ∧
        ControlPath (decodedControlGraph p) start.pc exit compressed ∧
        compressed.Sublist anchors ∧
        (∀ node, node ∈ anchors → node ∈ compressed) ∧
        SuccessfulPath (decodedControlGraph p) start.pc
          (compressed ++ [functionReturn p (activeFunctionId root spine)]) ∧
        ActivationContinuationAt p root spine
          (functionReturn p (activeFunctionId root spine)) finish := by
  classical
  obtain ⟨exitStep, output, hexitPositive, hexitBound, hactivationLive,
    hfinishStack, hlookup, hfunction, hop⟩ :=
    successful_execution_first_activation_exit hexecution hstartStack hspine
  let prefixFuel := exitStep - 1
  have hprefixBound : prefixFuel < steps := by
    dsimp [prefixFuel]
    omega
  have hpointwise : ∀ elapsed, elapsed < prefixFuel →
      AnchoredStep p spine (runPrefix p elapsed start).state
        (step p (runPrefix p elapsed start).state).state := by
    intro elapsed helapsed
    have hleftActive := hexecution.reached_active (elapsed := elapsed) (by omega)
    have hrightActiveRaw := hexecution.reached_active (elapsed := elapsed + 1) (by omega)
    obtain ⟨leftPrefix, hleftStack⟩ := hactivationLive elapsed (by omega)
    obtain ⟨rightPrefix, hrightStack⟩ := hactivationLive (elapsed + 1) (by omega)
    obtain ⟨leftNode, hleftAnchor⟩ := ActivationAnchor.exists_of_suffix hleftStack
    have hnextState : (runPrefix p (elapsed + 1) start).state =
        (step p (runPrefix p elapsed start).state).state := by
      have hadd := congrArg StepResult.state
        (ReleaseSynchronization.runPrefix_add p elapsed 1 start)
      simpa only [runPrefix] using hadd
    have hrightActive : ActiveState p root
        (step p (runPrefix p elapsed start).state).state := by
      rw [← hnextState]
      exact hrightActiveRaw
    have hrightStack' :
        (step p (runPrefix p elapsed start).state).state.callStack =
          rightPrefix ++ spine := by
      rw [← hnextState]
      exact hrightStack
    obtain ⟨rightNode, hrightAnchor⟩ := ActivationAnchor.exists_of_suffix hrightStack'
    exact live_step_is_anchored hleftActive hrightActive hleftAnchor hrightAnchor
  obtain ⟨finish, exit, anchors, hfinish, hrawPath⟩ :=
    anchoredRawPath_of_runPrefix prefixFuel start start.pc (.current hstartStack) hpointwise
  obtain ⟨compressed, hcontrol, hsublist, hcover⟩ :=
    hrawPath.toStutteringControlPath.toControlPath_cover
  have hfinishBefore : finish = (runPrefix p (exitStep - 1) start).state := by
    simpa [prefixFuel] using hfinish
  have hexitAnchor := hrawPath.endAnchor
  rw [hfinishBefore] at hexitAnchor
  have hexitEq : exit = (runPrefix p (exitStep - 1) start).state.pc :=
    hexitAnchor.current_injective hfinishStack
  have hlastBound := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hgraphBound : (runPrefix p (exitStep - 1) start).state.pc <
      (decodedControlGraph p).size := by
    simp [ControlGraph.size, decodedControlGraph]
    omega
  have hreturnEdge : functionReturn p (activeFunctionId root spine) ∈
      (decodedControlGraph p).successors.getD
        (runPrefix p (exitStep - 1) start).state.pc [] := by
    rw [decodedControlGraph_instruction_edges p _ hlastBound]
    have hlastGet : p.instructions[(runPrefix p (exitStep - 1) start).state.pc] = output :=
      (Array.getElem?_eq_some_iff.mp hlookup).2
    rw [hlastGet]
    simp [instructionSuccessors, hop, hfunction]
  have hsuccessfulExit : functionReturn p (activeFunctionId root spine) ∈
      (decodedControlGraph p).successfulExits := by
    simp only [decodedControlGraph, functionReturn]
    rw [List.mem_range'_1]
    omega
  have hsuccessful : SuccessfulPath (decodedControlGraph p) start.pc
      (compressed ++ [functionReturn p (activeFunctionId root spine)]) := by
    refine ⟨functionReturn p (activeFunctionId root spine), hsuccessfulExit, ?_⟩
    have hcontrol' := hcontrol
    rw [hexitEq] at hcontrol'
    exact append_control_edge hcontrol' hgraphBound hreturnEdge
  have hcontinuation : ActivationContinuationAt p root spine
      (functionReturn p (activeFunctionId root spine)) finish := by
    right
    refine ⟨rfl, ?_, output, ?_, hfunction, Or.inl hop⟩
    · simpa [hfinishBefore] using hfinishStack
    · simpa [hfinishBefore] using hlookup
  exact ⟨exitStep, finish, exit, anchors, compressed, hexitPositive, hexitBound,
    hfinishBefore, hrawPath, hcontrol, hsublist, hcover, hsuccessful, hcontinuation⟩

/-- Uniform activation witness.  For the root, `fuel` is the last live top-level state.  For a
    nested activation it is the last live state before the first frame-coherent return. -/
theorem successful_activation_control_witness {p : SemanticProgram}
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hexecution : SuccessfulExecution p root steps start result)
    (hstartStack : start.callStack = spine)
    (hactivePositive : 0 < (activeFunctionId root spine).toNat)
    (hactiveBound : (activeFunctionId root spine).toNat ≤ p.functions.size) :
    ∃ fuel finish exit anchors compressed,
      fuel < steps ∧ finish = (runPrefix p fuel start).state ∧
        AnchoredRawPath p spine fuel start start.pc finish exit anchors ∧
        ControlPath (decodedControlGraph p) start.pc exit compressed ∧
        compressed.Sublist anchors ∧
        (∀ node, node ∈ anchors → node ∈ compressed) ∧
        SuccessfulPath (decodedControlGraph p) start.pc
          (compressed ++ [functionReturn p (activeFunctionId root spine)]) ∧
        ActivationContinuationAt p root spine
          (functionReturn p (activeFunctionId root spine)) finish := by
  classical
  by_cases hspine : spine = []
  · have hstartEmpty : start.callStack = [] := hstartStack.trans hspine
    have hrootPositive : 0 < root.toNat := by
      simpa [hspine, activeFunctionId] using hactivePositive
    have hrootBound : root.toNat ≤ p.functions.size := by
      simpa [hspine, activeFunctionId] using hactiveBound
    rw [hspine]
    obtain ⟨finish, exit, anchors, compressed, hfinish, hrawPath, hcontrol,
      hsublist, hcover, hsuccessful⟩ :=
      successful_root_execution_control_witness hexecution hstartEmpty
        hrootPositive hrootBound
    have hlast := hexecution.lastTopLevel
    dsimp only at hlast
    obtain ⟨hstack, instruction, hlookup, hop⟩ := hlast
    have hactive := hexecution.reached_active (elapsed := steps - 1) (by
      have := hexecution.positive
      omega)
    obtain ⟨active, hactiveLookup, hactiveFunction⟩ := hactive.currentInstruction
    have hinstruction : active = instruction := by
      rw [hlookup] at hactiveLookup
      exact Option.some.inj hactiveLookup.symm
    subst active
    have hfunction : instruction.functionId = root := by
      simpa [hstack, activeFunctionId] using hactiveFunction
    have hcontinuation : ActivationContinuationAt p root [] (functionReturn p root) finish := by
      right
      refine ⟨by simp [activeFunctionId], ?_, instruction, ?_, ?_, ?_⟩
      · simpa [hfinish] using hstack
      · simpa [hfinish] using hlookup
      · simpa [activeFunctionId] using hfunction
      · exact hop.imp_right (fun hhalt => ⟨rfl, hhalt⟩)
    refine ⟨steps - 1, finish, exit, anchors, compressed, by
      have := hexecution.positive
      omega
      , hfinish,
      hrawPath, hcontrol, hsublist, hcover, ?_, ?_⟩
    · simpa [activeFunctionId] using hsuccessful
    · simpa [activeFunctionId] using hcontinuation
  · obtain ⟨exitStep, finish, exit, anchors, compressed, _, hexitBound,
      hfinish, hrawPath, hcontrol, hsublist, hcover, hsuccessful, hcontinuation⟩ :=
      successful_nonroot_activation_control_witness hexecution hstartStack hspine
        hactivePositive hactiveBound
    exact ⟨exitStep - 1, finish, exit, anchors, compressed, by omega, hfinish,
      hrawPath, hcontrol, hsublist, hcover, hsuccessful, hcontinuation⟩

/-- The v9 raw machine raises only occurrence labels. It does not alter any decoded control edge,
    function return vertex, or successful exit. -/
theorem decodedControlGraph_rawSemanticProgram (program : V9.Program)
    (analysis : V9.OccurrenceDataflowInvocation.Analysis) :
    decodedControlGraph (rawSemanticProgram program analysis) =
      decodedControlGraph (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow) := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  unfold decodedControlGraph
  apply congrArg₂ ControlGraph.mk
  · apply Array.ext
    · simp [rawSemanticProgram]
    · intro position hleft hright
      simp only [Array.getElem_append]
      by_cases hposition : position < base.instructions.size
      · simp [hposition, rawSemanticProgram, base, raiseInstructionResultLabel,
          raiseInstructionOccurrence,
          instructionSuccessors, functionReturn]
      · simp [hposition, rawSemanticProgram, base]
  · simp [rawSemanticProgram]

/-- Recover the exact unraised decoded instruction underneath a raw-machine lookup.  The equality
    records the only transformation performed by `rawSemanticProgram`; in particular calls,
    operands, targets, and function ownership are unchanged. -/
theorem rawInstructionSource_of_lookup
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction) :
    ∃ source,
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions[pc]? =
          some source ∧
        instruction = raiseInstructionResultLabel
          (occurrenceValueLabels analysis
            (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow))
          (raiseInstructionOccurrence source
            (if source.op == .output then
              localOccurrenceAt analysis.localAnalysis.frontiers pc
            else effectiveOccurrence analysis source pc)
            (rootReturnOccurrence?
              (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow) analysis source)) := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hrawBound := (Array.getElem?_eq_some_iff.mp hlookup).1
  have hbound : pc < base.instructions.size := by
    simpa [rawSemanticProgram, base] using hrawBound
  let source := base.instructions[pc]
  have hsource : base.instructions[pc]? = some source := by
    exact Array.getElem?_eq_getElem hbound
  refine ⟨source, by simpa [base] using hsource, ?_⟩
  have hrawGet := (Array.getElem?_eq_some_iff.mp hlookup).2
  simpa [rawSemanticProgram, base, source, hbound] using hrawGet.symm

private theorem invocationInfluence_local_component {caller localLane selection sink : Label}
    (hflow : ((caller.lub localLane).lub selection).flowsTo sink = true) :
    localLane.flowsTo sink = true := by
  cases caller <;> cases localLane <;> cases selection <;> cases sink <;>
    simp_all [Label.flowsTo, Label.lub, Label.rank]

private theorem invocationInfluence_caller_component {caller localLane selection sink : Label}
    (hflow : ((caller.lub localLane).lub selection).flowsTo sink = true) :
    caller.flowsTo sink = true := by
  cases caller <;> cases localLane <;> cases selection <;> cases sink <;>
    simp_all [Label.flowsTo, Label.lub, Label.rank]

private theorem labelFlows_trans {first middle last : Label}
    (hfirst : first.flowsTo middle = true) (hlast : middle.flowsTo last = true) :
    first.flowsTo last = true := by
  cases first <;> cases middle <;> cases last <;>
    simp_all [Label.flowsTo, Label.rank]

private theorem invocationSite_call_ne_none
    (machine : SemanticProgram) (frontiers : ThresholdFrontiers)
    {pc : Nat} {instruction : Instruction}
    (hlookup : machine.instructions[pc]? = some instruction)
    (hcall : instruction.op = .call ∨ instruction.op = .closure) :
    invocationSite? machine frontiers pc ≠ some none := by
  unfold invocationSite?
  simp only [hlookup, bind, Option.bind_some]
  rcases hcall with hop | hop
  · rw [hop]
    simp only
    split
    · simp
    · cases functionOperand? machine instruction with
      | none => simp
      | some callee =>
          simp only [Option.bind_some]
          split <;> simp
  · rw [hop]
    simp only
    split
    · simp
    · cases (valueOperandCells machine instruction).head? <;> simp

/-- Every decoded call/closure site returned by v9 analysis has a concrete checked invocation
    record.  This is extracted from the executable all-instruction postcheck, not supplied by the
    relational proof. -/
theorem analyzed_call_site
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction}
    (hlookup :
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions[pc]? =
        some instruction)
    (hcall : instruction.op = .call ∨ instruction.op = .closure) :
    ∃ site,
      invocationSite?
          (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)
          analysis.localAnalysis.frontiers pc = some (some site) ∧
        (siteInfluence analysis.labels site).flowsTo
          (labelAt analysis.labels site.destination) = true := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hchecks :=
    (V9.OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).2.2.2.2
  have hpc : pc < base.instructions.size := by
    exact (Array.getElem?_eq_some_iff.mp (by simpa [base] using hlookup)).1
  have hchecked :
      (match invocationSite? base analysis.localAnalysis.frontiers pc with
       | none => false
       | some none => true
       | some (some site) =>
          (siteInfluence analysis.labels site).flowsTo
            (labelAt analysis.labels site.destination)) = true := by
    simp only [invocationChecks, Bool.and_eq_true] at hchecks
    exact (List.all_eq_true.mp hchecks.1.2) pc (List.mem_range.mpr hpc)
  cases hsite : invocationSite? base analysis.localAnalysis.frontiers pc with
  | none => simp [hsite] at hchecked
  | some result =>
      cases result with
      | none =>
          exact False.elim (invocationSite_call_ne_none base
            analysis.localAnalysis.frontiers (by simpa [base] using hlookup) hcall hsite)
      | some site =>
          exact ⟨site, rfl, by simpa [hsite] using hchecked⟩

private theorem invocationSite_direct_shape
    (machine : SemanticProgram) (frontiers : ThresholdFrontiers)
    {pc : Nat} {instruction : Instruction} {calleeId : UInt32} {site : InvocationSite}
    (hlookup : machine.instructions[pc]? = some instruction)
    (hop : instruction.op = .call)
    (htarget : functionOperand? machine instruction = some calleeId)
    (hsite : invocationSite? machine frontiers pc = some (some site)) :
    site = ⟨instruction.functionId, calleeId,
      localOccurrenceAt frontiers pc, .pub, false⟩ := by
  unfold invocationSite? at hsite
  simp only [hlookup, bind, Option.bind_some] at hsite
  rw [hop] at hsite
  simp only at hsite
  split at hsite
  · contradiction
  · rw [htarget] at hsite
    simp only [Option.bind_some] at hsite
    split at hsite
    · contradiction
    · exact Option.some.inj (Option.some.inj hsite).symm

private theorem invocationSite_closure_shape
    (machine : SemanticProgram) (frontiers : ThresholdFrontiers)
    {pc : Nat} {instruction : Instruction} {site : InvocationSite}
    (hlookup : machine.instructions[pc]? = some instruction)
    (hop : instruction.op = .closure)
    (hsite : invocationSite? machine frontiers pc = some (some site)) :
    ∃ selector,
      (valueOperandCells machine instruction).head? = some selector ∧
        site = ⟨instruction.functionId, dynamicCell machine,
          localOccurrenceAt frontiers pc,
          labelAt machine.valueLabels selector, true⟩ := by
  unfold invocationSite? at hsite
  simp only [hlookup, bind, Option.bind_some] at hsite
  rw [hop] at hsite
  simp only at hsite
  split at hsite
  · contradiction
  · cases hselector : (valueOperandCells machine instruction).head? with
    | none => simp [hselector] at hsite
    | some selector =>
        refine ⟨selector, rfl, ?_⟩
        rw [hselector] at hsite
        simp only [Option.bind_some] at hsite
        have heq : (⟨instruction.functionId, dynamicCell machine,
            localOccurrenceAt frontiers pc, labelAt machine.valueLabels selector, true⟩ :
            InvocationSite) = site := by
          exact Option.some.inj (Option.some.inj hsite)
        exact heq.symm

/-- Local control at a checked direct/closure call reaches the invocation label of every callee
    admitted by that call.  Closure calls use the verifier's shared dynamic-target vertex, whose
    checked fan-out covers every decoded function; no runtime selector value is assumed. -/
theorem analyzed_call_local_occurrence_flows_to_callee
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction} {calleeId : UInt32} {callee : Function}
    (hlookup :
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions[pc]? =
        some instruction)
    (hcall : instruction.op = .call ∨ instruction.op = .closure)
    (hcallee : functionById?
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow) calleeId = some callee)
    (hdirect : instruction.op = .call →
      functionOperand? (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)
        instruction = some calleeId) :
    (localOccurrenceAt analysis.localAnalysis.frontiers pc).flowsTo
      (labelAt analysis.labels calleeId) = true := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  obtain ⟨site, hsite, hflow⟩ := analyzed_call_site hanalysis hlookup hcall
  rcases hcall with hop | hop
  · have htarget := hdirect hop
    have hsiteShape := invocationSite_direct_shape base analysis.localAnalysis.frontiers
      (by simpa [base] using hlookup) hop (by simpa [base] using htarget)
      (by simpa [base] using hsite)
    subst site
    exact invocationInfluence_local_component hflow
  · obtain ⟨selector, _, hsiteShape⟩ := invocationSite_closure_shape base
      analysis.localAnalysis.frontiers (by simpa [base] using hlookup) hop
      (by simpa [base] using hsite)
    subst site
    have hlocalDynamic := invocationInfluence_local_component hflow
    have hcalleeMem : callee ∈ base.functions := by
      exact Array.mem_of_find?_eq_some (by simpa [base, functionById?] using hcallee)
    have hcalleeId : callee.id = calleeId := by
      have hid := Array.find?_some
        (p := fun function : Function => function.id == calleeId)
        (xs := base.functions) (a := callee)
        (by simpa [base, functionById?] using hcallee)
      exact beq_iff_eq.mp hid
    have hchecks :=
      (V9.OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).2.2.2.2
    simp only [invocationChecks, Bool.and_eq_true] at hchecks
    obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hcalleeMem
    have hdynamic := Array.all_eq_true.mp hchecks.2 position hposition
    exact labelFlows_trans hlocalDynamic (by
      simpa [base, heq, hcalleeId] using hdynamic)

/-- The suspended caller's invocation summary is also a lower bound of every callee admitted by
    a checked direct/closure site.  This is the frame-chain component of transitive occurrence
    propagation; unlike the local component above it composes through arbitrarily deep calls. -/
theorem analyzed_call_caller_occurrence_flows_to_callee
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {pc : Nat} {instruction : Instruction} {calleeId : UInt32} {callee : Function}
    (hlookup :
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions[pc]? =
        some instruction)
    (hcall : instruction.op = .call ∨ instruction.op = .closure)
    (hcallee : functionById?
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow) calleeId = some callee)
    (hdirect : instruction.op = .call →
      functionOperand? (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)
        instruction = some calleeId) :
    (labelAt analysis.labels instruction.functionId).flowsTo
      (labelAt analysis.labels calleeId) = true := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  obtain ⟨site, hsite, hflow⟩ := analyzed_call_site hanalysis hlookup hcall
  rcases hcall with hop | hop
  · have htarget := hdirect hop
    have hsiteShape := invocationSite_direct_shape base analysis.localAnalysis.frontiers
      (by simpa [base] using hlookup) hop (by simpa [base] using htarget)
      (by simpa [base] using hsite)
    subst site
    exact invocationInfluence_caller_component hflow
  · obtain ⟨selector, _, hsiteShape⟩ := invocationSite_closure_shape base
      analysis.localAnalysis.frontiers (by simpa [base] using hlookup) hop
      (by simpa [base] using hsite)
    subst site
    have hcallerDynamic := invocationInfluence_caller_component hflow
    have hcalleeMem : callee ∈ base.functions := by
      exact Array.mem_of_find?_eq_some (by simpa [base, functionById?] using hcallee)
    have hcalleeId : callee.id = calleeId := by
      have hid := Array.find?_some
        (p := fun function : Function => function.id == calleeId)
        (xs := base.functions) (a := callee)
        (by simpa [base, functionById?] using hcallee)
      exact beq_iff_eq.mp hid
    have hchecks :=
      (V9.OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).2.2.2.2
    simp only [invocationChecks, Bool.and_eq_true] at hchecks
    obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hcalleeMem
    have hdynamic := Array.all_eq_true.mp hchecks.2 position hposition
    exact labelFlows_trans hcallerDynamic (by
      simpa [base, heq, hcalleeId] using hdynamic)

/-- A coherent raw frame identifies an exact decoded call/closure site.  The v9 invocation
    postcheck therefore propagates that site's local occurrence to the suspended callee's
    invocation label.  Closure targets use the checked all-functions summary. -/
theorem coherent_frame_local_occurrence_flows_to_callee
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {caller : UInt32} {frame : CallFrame}
    (hframe : FrameDeclarationCoherent (rawSemanticProgram program analysis) caller frame) :
    (localOccurrenceAt analysis.localAnalysis.frontiers (frame.returnPc - 1)).flowsTo
      (labelAt analysis.labels frame.calleeId) = true := by
  let machine := rawSemanticProgram program analysis
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  obtain ⟨callerDeclaration, callee, call, continuation, hcaller, hcallee, hpositive,
    hcall, hcallFunction, hcallOp, hdestination, hdirect, hcontinuation,
    hcontinuationFunction, hreturnLabel, hsaved⟩ := hframe
  obtain ⟨source, hsource, hraised⟩ := rawInstructionSource_of_lookup hcall
  have hsourceOp : source.op = call.op := by
    rw [hraised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
  have hsourceCall : source.op = .call ∨ source.op = .closure := by
    rcases hcallOp with hop | hop
    · exact Or.inl (hsourceOp.trans hop)
    · exact Or.inr (hsourceOp.trans hop)
  have hcalleeBase : functionById? base frame.calleeId = some callee := by
    simpa only [machine, base, rawSemanticProgram, functionById?] using hcallee
  have hdirectBase : source.op = .call →
      functionOperand? base source = some frame.calleeId := by
    intro hop
    have hcallDirect : call.op = .call := hsourceOp.symm.trans hop
    have htarget := hdirect hcallDirect
    simpa [functionOperand?, instructionOperands, instructionOperandAt?, machine, base,
      rawSemanticProgram, hraised, raiseInstructionResultLabel,
      raiseInstructionOccurrence] using htarget
  exact analyzed_call_local_occurrence_flows_to_callee hanalysis
    (by simpa [base] using hsource) hsourceCall hcalleeBase hdirectBase

/-- The invocation label of a coherent frame's caller flows to the frame's callee label.  The
    declaration coherence fixes the real call site and direct target; closure fan-out remains the
    verifier's conservative all-functions summary. -/
theorem coherent_frame_caller_occurrence_flows_to_callee
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {caller : UInt32} {frame : CallFrame}
    (hframe : FrameDeclarationCoherent (rawSemanticProgram program analysis) caller frame) :
    (labelAt analysis.labels caller).flowsTo
      (labelAt analysis.labels frame.calleeId) = true := by
  let machine := rawSemanticProgram program analysis
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  obtain ⟨callerDeclaration, callee, call, continuation, hcaller, hcallee, hpositive,
    hcall, hcallFunction, hcallOp, hdestination, hdirect, hcontinuation,
    hcontinuationFunction, hreturnLabel, hsaved⟩ := hframe
  obtain ⟨source, hsource, hraised⟩ := rawInstructionSource_of_lookup hcall
  have hsourceOp : source.op = call.op := by
    rw [hraised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
  have hsourceFunction : source.functionId = caller := by
    rw [hraised] at hcallFunction
    simpa [raiseInstructionResultLabel, raiseInstructionOccurrence] using hcallFunction
  have hsourceCall : source.op = .call ∨ source.op = .closure := by
    rcases hcallOp with hop | hop
    · exact Or.inl (hsourceOp.trans hop)
    · exact Or.inr (hsourceOp.trans hop)
  have hcalleeBase : functionById? base frame.calleeId = some callee := by
    simpa only [machine, base, rawSemanticProgram, functionById?] using hcallee
  have hdirectBase : source.op = .call →
      functionOperand? base source = some frame.calleeId := by
    intro hop
    have hcallDirect : call.op = .call := hsourceOp.symm.trans hop
    have htarget := hdirect hcallDirect
    simpa [functionOperand?, instructionOperands, instructionOperandAt?, machine, base,
      rawSemanticProgram, hraised, raiseInstructionResultLabel,
      raiseInstructionOccurrence] using htarget
  have hflow := analyzed_call_caller_occurrence_flows_to_callee hanalysis
    (by simpa [base] using hsource) hsourceCall hcalleeBase hdirectBase
  simpa [hsourceFunction] using hflow

/-- Invocation influence composes along the genuine declaration-coherent stack, from the named
    root of that stack to its currently active callee. -/
theorem frameChain_root_occurrence_flows_to_active
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {stack : List CallFrame}
    (hchain : FrameChainCoherent (rawSemanticProgram program analysis) root stack) :
    (labelAt analysis.labels root).flowsTo
      (labelAt analysis.labels (activeFunctionId root stack)) = true := by
  induction stack with
  | nil =>
      change (labelAt analysis.labels root).flowsTo (labelAt analysis.labels root) = true
      generalize labelAt analysis.labels root = label
      cases label <;> decide
  | cons frame rest ih =>
      exact labelFlows_trans (ih hchain.2)
        (coherent_frame_caller_occurrence_flows_to_callee hanalysis hchain.1)

private theorem activeFunctionId_append_outer (root : UInt32)
    (inner : List CallFrame) (outer : CallFrame) (spine : List CallFrame) :
    activeFunctionId root (inner ++ outer :: spine) = activeFunctionId outer.calleeId inner := by
  cases inner <;> simp [activeFunctionId]

/-- Split a genuine coherent stack at an activation anchor.  The lower witness is the exact
    suspended frame at that anchor; the upper witness is a coherent nested-call chain rooted in
    that frame's callee. -/
theorem frameChain_split_activation
    {machine : SemanticProgram} {root : UInt32}
    {inner spine : List CallFrame} {outer : CallFrame}
    (hchain : FrameChainCoherent machine root (inner ++ outer :: spine)) :
    FrameDeclarationCoherent machine (activeFunctionId root spine) outer ∧
      FrameChainCoherent machine outer.calleeId inner := by
  induction inner with
  | nil => exact ⟨hchain.1, trivial⟩
  | cons frame rest ih =>
      have htail := ih hchain.2
      refine ⟨htail.1, ?_⟩
      refine ⟨?_, htail.2⟩
      simpa [activeFunctionId_append_outer root rest outer spine] using hchain.1

/-- Every activation anchor in a live raw state names a real decoded instruction.  Current
    anchors are the state's instruction cursor; descendant anchors are the genuine call site
    retained by the declaration-coherent outer frame.  In particular, no activation anchor can
    be one of the synthetic function-return vertices appended after the instruction array. -/
theorem active_activationAnchor_lt_instructions {machine : SemanticProgram} {root : UInt32}
    {spine : List CallFrame} {anchor : Nat} {state : State}
    (hactive : ActiveState machine root state)
    (hanchor : ActivationAnchor spine anchor state) :
    anchor < machine.instructions.size := by
  cases hanchor with
  | current _ =>
      obtain ⟨instruction, hlookup, _⟩ := hactive.currentInstruction
      exact (Array.getElem?_eq_some_iff.mp hlookup).1
  | descendant inner outer hstack =>
      have hchain := hactive.frameChain
      rw [hstack] at hchain
      obtain ⟨houter, _⟩ := frameChain_split_activation hchain
      obtain ⟨_, _, _, _, _, _, _, hcall, _, _, _, _, _, _, _, _⟩ := houter
      exact (Array.getElem?_eq_some_iff.mp hcall).1

private theorem activeFunctionId_append_suffix (root : UInt32)
    (privateFrames suffix : List CallFrame) :
    activeFunctionId root (privateFrames ++ suffix) =
      activeFunctionId (activeFunctionId root suffix) privateFrames := by
  cases privateFrames <;> simp [activeFunctionId]

/-- The coherent frames strictly above an activation suffix form a coherent chain rooted at that
    activation's active function.  This is the stack analogue of dropping a raw execution prefix. -/
theorem frameChain_prefix_above_suffix
    {machine : SemanticProgram} {root : UInt32}
    {privateFrames suffix : List CallFrame}
    (hchain : FrameChainCoherent machine root (privateFrames ++ suffix)) :
    FrameChainCoherent machine (activeFunctionId root suffix) privateFrames := by
  induction privateFrames with
  | nil => trivial
  | cons frame rest ih =>
      refine ⟨?_, ih hchain.2⟩
      simpa [activeFunctionId_append_suffix root rest suffix] using hchain.1

private theorem labelFlows_lub_left (left right : Label) :
    left.flowsTo (left.lub right) = true := by
  cases left <;> cases right <;> decide

/-- Away from an internal return, the active function's invocation summary is an actual lower
    bound on the raw occurrence-raised block. -/
theorem invocation_occurrence_flows_to_raw_block_of_lookup
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    {pc : Nat} {instruction : Instruction}
    (hlookup : (rawSemanticProgram program analysis).instructions[pc]? = some instruction)
    (hnonoutput : instruction.op ≠ .output) :
    (labelAt analysis.labels instruction.functionId).flowsTo instruction.blockLabel = true := by
  obtain ⟨source, hsource, hraised⟩ := rawInstructionSource_of_lookup hlookup
  have hsourceOp : source.op = instruction.op := by
    rw [hraised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
  have hsourceNonoutput : source.op ≠ .output := by
    intro houtput
    exact hnonoutput (hsourceOp.symm.trans houtput)
  have hsourceFunction : source.functionId = instruction.functionId := by
    rw [hraised]
    simp [raiseInstructionResultLabel, raiseInstructionOccurrence]
  have htoEffective : (labelAt analysis.labels source.functionId).flowsTo
      (effectiveOccurrence analysis source pc) = true := by
    exact labelFlows_lub_left _ _
  have htoRaised := labelFlows_trans htoEffective
    (derived_occurrence_flows_to_raised_block source
      (effectiveOccurrence analysis source pc)
      (rootReturnOccurrence?
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow) analysis source)
      hsourceNonoutput)
  rw [hraised]
  simpa [hsourceNonoutput, raiseInstructionResultLabel, raiseInstructionOccurrence] using htoRaised

/-- A checked controller edge that participates in a finite successful decoded path must hit the
    verifier-owned parent continuation. This derives ancestry from the checked edge and liveness;
    no merge operand or supplied postdominator proposition is used. -/
theorem checked_controller_parent_hits_successful_path {graph : ControlGraph}
    {index : EscapeIndex} (hindex : escapeIndexChecks graph index = true)
    {controller arm : Nat} {trace : List Nat}
    (hcontroller : controller < graph.size)
    (hedge : arm ∈ graph.successors.getD controller [])
    (hpath : SuccessfulPath graph arm trace) : index.parentAt controller ∈ trace := by
  have hindex' := hindex
  simp only [escapeIndexChecks, Bool.and_eq_true] at hindex
  obtain ⟨⟨⟨⟨hgraph, hparentSize⟩, hrankSize⟩, hexits⟩, hnodes⟩ := hindex
  have hgraphFacts := hgraph
  simp only [ControlGraph.wellFormedB, Bool.and_eq_true, List.all_eq_true,
    Array.all_eq_true, decide_eq_true_eq] at hgraphFacts
  simp only [List.all_eq_true, Bool.and_eq_true] at hnodes
  have harmBound : arm < graph.size := by
    have hsource : controller < graph.successors.size := hcontroller
    exact hgraphFacts.2 controller hsource arm (by simpa [Array.getD, hsource] using hedge)
  have harmLive : index.liveB arm = true :=
    (checked_live_iff_successful_path hindex' harmBound).mpr ⟨trace, hpath⟩
  have hedgeChecked := (hnodes controller (List.mem_range.mpr hcontroller)).2 arm hedge
  simp only [edgeParentB, harmLive, Bool.not_true, Bool.false_or,
    Bool.and_eq_true] at hedgeChecked
  exact checked_ancestor_forces_successful_hit hindex' hedgeChecked.2 hpath

/-- Load-bearing arbitrary-activation bridge.  From the actual successful raw suffix beginning at
    a controller arm, it returns the earliest exact raw prefix that realizes the verifier-owned
    parent continuation.  `spine` may be nonempty; balanced direct/closure calls and recursion
    stutter at activation anchors and frame-coherent returns take checked summary edges. -/
theorem successful_execution_first_continuation_hit {p : SemanticProgram}
    {root : UInt32} {steps controller arm : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hexecution : SuccessfulExecution p root steps start result)
    (hstartStack : start.callStack = spine) (hstartPc : start.pc = arm)
    (hactivePositive : 0 < (activeFunctionId root spine).toNat)
    (hactiveBound : (activeFunctionId root spine).toNat ≤ p.functions.size)
    {index : EscapeIndex}
    (hindex : escapeIndexChecks (decodedControlGraph p) index = true)
    (hcontroller : controller < (decodedControlGraph p).size)
    (hedge : arm ∈ (decodedControlGraph p).successors.getD controller []) :
    ∃ elapsed, elapsed < steps ∧
      ActivationContinuationAt p root spine (index.parentAt controller)
        (runPrefix p elapsed start).state ∧
      ∀ earlier, earlier < elapsed →
        ¬ ActivationContinuationAt p root spine (index.parentAt controller)
          (runPrefix p earlier start).state := by
  classical
  obtain ⟨fuel, finish, exit, anchors, compressed, hfuel, hfinish, hrawPath,
    hcontrol, hsublist, hcover, hsuccessful, hreturnAt⟩ :=
    successful_activation_control_witness hexecution hstartStack hactivePositive hactiveBound
  rw [hstartPc] at hsuccessful
  have hhit := checked_controller_parent_hits_successful_path hindex hcontroller hedge hsuccessful
  have hmember : index.parentAt controller ∈ compressed ∨
      index.parentAt controller = functionReturn p (activeFunctionId root spine) := by
    simpa only [List.mem_append, List.mem_singleton] using hhit
  have hexists : ∃ elapsed, elapsed < steps ∧
      ActivationContinuationAt p root spine (index.parentAt controller)
        (runPrefix p elapsed start).state := by
    rcases hmember with hcompressed | hreturn
    · have hanchors : index.parentAt controller ∈ anchors := hsublist.subset hcompressed
      obtain ⟨elapsed, helapsed, hanchor, _⟩ := hrawPath.first_anchor_hit hanchors
      exact ⟨elapsed, by omega, Or.inl hanchor⟩
    · refine ⟨fuel, hfuel, ?_⟩
      rw [hfinish] at hreturnAt
      simpa [hreturn] using hreturnAt
  let elapsed := Nat.find hexists
  have hspec := Nat.find_spec hexists
  refine ⟨elapsed, hspec.1, hspec.2, ?_⟩
  intro earlier hearlier hearlierHit
  exact Nat.find_min hexists hearlier ⟨by omega, hearlierHit⟩

/-- Exact earliest raw realization of any checked parent on the successful root path.  Calls,
    closures and recursion are represented by stuttering activation anchors; returns take only
    frame-coherent summary edges.  A synthetic return is realized at its genuine last live state,
    never as an invented program counter. -/
theorem successful_root_execution_first_continuation_hit {p : SemanticProgram}
    {root : UInt32} {steps controller arm : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution p root steps start result)
    (hstartStack : start.callStack = []) (hstartPc : start.pc = arm)
    (hrootPositive : 0 < root.toNat) (hrootBound : root.toNat ≤ p.functions.size)
    {index : EscapeIndex}
    (hindex : escapeIndexChecks (decodedControlGraph p) index = true)
    (hcontroller : controller < (decodedControlGraph p).size)
    (hedge : arm ∈ (decodedControlGraph p).successors.getD controller []) :
    ∃ elapsed, elapsed < steps ∧
      ActivationContinuationAt p root [] (index.parentAt controller)
        (runPrefix p elapsed start).state ∧
      ∀ earlier, earlier < elapsed →
        ¬ ActivationContinuationAt p root [] (index.parentAt controller)
          (runPrefix p earlier start).state := by
  classical
  have hstepsPositive := hexecution.positive
  obtain ⟨_, _, anchors, compressed, _, hrawPath, _, hsublist, _, hsuccessful⟩ :=
    successful_root_execution_control_witness hexecution hstartStack hrootPositive hrootBound
  rw [hstartPc] at hsuccessful
  have hhit := checked_controller_parent_hits_successful_path hindex hcontroller hedge hsuccessful
  have hmember : index.parentAt controller ∈ compressed ∨
      index.parentAt controller = functionReturn p root := by
    simpa only [List.mem_append, List.mem_singleton] using hhit
  have hexists : ∃ elapsed, elapsed < steps ∧
      ActivationContinuationAt p root [] (index.parentAt controller)
        (runPrefix p elapsed start).state := by
    rcases hmember with hcompressed | hreturn
    · have hanchors : index.parentAt controller ∈ anchors := hsublist.subset hcompressed
      obtain ⟨elapsed, helapsed, hanchor, _⟩ := hrawPath.first_anchor_hit hanchors
      exact ⟨elapsed, by omega, Or.inl hanchor⟩
    · refine ⟨steps - 1, by omega, Or.inr ?_⟩
      have hlast := hexecution.lastTopLevel
      dsimp only at hlast
      obtain ⟨hstack, instruction, hlookup, hop⟩ := hlast
      have hactive := hexecution.reached_active (elapsed := steps - 1) (by omega)
      obtain ⟨active, hactiveLookup, hactiveFunction⟩ := hactive.currentInstruction
      have hinstruction : active = instruction := by
        rw [hlookup] at hactiveLookup
        exact Option.some.inj hactiveLookup.symm
      subst active
      have hfunction : instruction.functionId = root := by
        simpa [hstack, activeFunctionId] using hactiveFunction
      exact ⟨by simpa [activeFunctionId] using hreturn,
        hstack, instruction, hlookup, by simpa [activeFunctionId] using hfunction,
        hop.imp_right (fun hhalt => ⟨rfl, hhalt⟩)⟩
  let elapsed := Nat.find hexists
  have hspec := Nat.find_spec hexists
  refine ⟨elapsed, hspec.1, hspec.2, ?_⟩
  intro earlier hearlier hearlierHit
  exact Nat.find_min hexists hearlier ⟨by omega, hearlierHit⟩

/-- Exactly the two ordinary private lanes.  SecretCT has no constructor here: its use as a
    controller is rejected by the separate raw SecretCT policy rather than being reclassified as
    ordinary private control.  An inherited lane is accepted through `controllerActiveB`, so the
    evidence covers both a directly private selector and a controller reached under private pc. -/
inductive PrivateControllerLane (graph : ControlGraph) (analysis : DecodedOccurrence.Analysis)
    (controller : Nat) : Label → Prop
  | internal
      (active : controllerActiveB graph analysis.selectors
        analysis.frontiers.internalLane 1 controller = true) :
      PrivateControllerLane graph analysis controller .internal
  | secret
      (active : controllerActiveB graph analysis.selectors
        analysis.frontiers.secretLane 2 controller = true) :
      PrivateControllerLane graph analysis controller .secret

/-- Every live decoded prefix after an Internal- or Secret-controlled edge remains in that
    exact occurrence lane until the verifier-owned continuation is reached.  The endpoint must
    have a real finite successful suffix; a dead arm cannot manufacture region evidence. -/
theorem checked_private_controller_prefix_is_nonpublic {graph : ControlGraph}
    {index : EscapeIndex} {analysis : DecodedOccurrence.Analysis}
    (htransfer : transferChecks graph index analysis.selectors analysis.frontiers = true)
    {controller arm target : Nat} {lane : Label} {trace : List Nat}
    (hlane : PrivateControllerLane graph analysis controller lane)
    (hcontroller : controller < graph.size)
    (hedge : arm ∈ graph.successors.getD controller [])
    (hpath : ControlPath graph arm target trace) (htarget : target < graph.size)
    (hcompletion : ∃ suffix, SuccessfulPath graph target suffix)
    (havoid : index.parentAt controller ∉ trace) :
    localOccurrenceAt analysis.frontiers target ≠ .pub := by
  simp only [transferChecks, Bool.and_eq_true] at htransfer
  cases hlane with
  | internal hactive =>
      have hpresent := checked_branch_prefix_lane_is_present htransfer.1.1.1 htransfer.1.1.2
        hcontroller hactive hedge hpath htarget hcompletion havoid
      have hflow := internal_lane_flows_to_local_occurrence hpresent
      intro hpublic
      simp [hpublic, Label.flowsTo, Label.rank] at hflow
  | secret hactive =>
      have hpresent := checked_branch_prefix_lane_is_present htransfer.1.1.1 htransfer.1.2
        hcontroller hactive hedge hpath htarget hcompletion havoid
      have hflow := secret_lane_flows_to_local_occurrence hpresent
      intro hpublic
      simp [hpublic, Label.flowsTo, Label.rank] at hflow

/-- Analysis fixes the one-based function layout.  Consequently the decoded root carried by a
    genuine active raw execution is positive and within the actual function array; callers do
    not provide these numerical facts. -/
theorem analyzed_successful_root_bounds {program : V9.Program}
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result) :
    0 < root.toNat ∧
      root.toNat ≤ (rawSemanticProgram program analysis).functions.size := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hrootChecks :=
    (V9.OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).2.2.2.1
  simp only [V9.OccurrenceDataflowInvocation.rootEntryChecks,
    Bool.and_eq_true] at hrootChecks
  have hrootLayout := hrootChecks.1.1
  simp only [V9.OccurrenceDataflowInvocation.rootLayoutChecks,
    Bool.and_eq_true] at hrootLayout
  have hfunctionLayout : OccurrenceInvocation.functionLayoutB base = true := by
    simpa [base] using hrootLayout.1.1.1
  obtain ⟨declaration, hdeclaration⟩ := hexecution.start_active.rootDeclared
  have hmemberRaw : declaration ∈ (rawSemanticProgram program analysis).functions := by
    exact Array.mem_of_find?_eq_some hdeclaration
  have hmember : declaration ∈ base.functions := by
    simpa [rawSemanticProgram, base] using hmemberRaw
  obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hmember
  simp only [OccurrenceInvocation.functionLayoutB, Bool.and_eq_true,
    List.all_eq_true] at hfunctionLayout
  have hrow := hfunctionLayout.2 position (List.mem_range.mpr hposition)
  simp only [Array.getElem?_eq_getElem hposition, heq, beq_iff_eq] at hrow
  have hid := Array.find?_some
    (p := fun function : Function => function.id == root)
    (xs := (rawSemanticProgram program analysis).functions)
    (a := declaration) hdeclaration
  have hid' : declaration.id = root := beq_iff_eq.mp hid
  rw [hid'] at hrow
  have hsize : (rawSemanticProgram program analysis).functions.size = base.functions.size := by
    simp [rawSemanticProgram, base]
  constructor
  · omega
  · rw [hsize]
    omega

/-- The invocation-active function of any genuine raw state also obeys the decoded one-based V9
    layout.  This is the bound needed by arbitrary nonempty activation convergence. -/
theorem analyzed_active_function_bounds {program : V9.Program}
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {state : State}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state) :
    0 < (activeFunctionId root state.callStack).toNat ∧
      (activeFunctionId root state.callStack).toNat ≤
        (rawSemanticProgram program analysis).functions.size := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hrootChecks :=
    (V9.OccurrenceDataflowInvocationSecurity.analyzed_components hanalysis).2.2.2.1
  simp only [V9.OccurrenceDataflowInvocation.rootEntryChecks,
    Bool.and_eq_true] at hrootChecks
  have hrootLayout := hrootChecks.1.1
  simp only [V9.OccurrenceDataflowInvocation.rootLayoutChecks,
    Bool.and_eq_true] at hrootLayout
  have hfunctionLayout : OccurrenceInvocation.functionLayoutB base = true := by
    simpa [base] using hrootLayout.1.1.1
  obtain ⟨declaration, hdeclaration⟩ := hactive.activeDeclared
  have hmemberRaw : declaration ∈ (rawSemanticProgram program analysis).functions :=
    Array.mem_of_find?_eq_some hdeclaration
  have hmember : declaration ∈ base.functions := by
    simpa [rawSemanticProgram, base] using hmemberRaw
  obtain ⟨position, hposition, heq⟩ := Array.mem_iff_getElem.mp hmember
  simp only [OccurrenceInvocation.functionLayoutB, Bool.and_eq_true,
    List.all_eq_true] at hfunctionLayout
  have hrow := hfunctionLayout.2 position (List.mem_range.mpr hposition)
  simp only [Array.getElem?_eq_getElem hposition, heq, beq_iff_eq] at hrow
  have hid := Array.find?_some
    (p := fun function : Function =>
      function.id == activeFunctionId root state.callStack)
    (xs := (rawSemanticProgram program analysis).functions)
    (a := declaration) hdeclaration
  have hid' : declaration.id = activeFunctionId root state.callStack := beq_iff_eq.mp hid
  rw [hid'] at hrow
  have hsize : (rawSemanticProgram program analysis).functions.size = base.functions.size := by
    simp [rawSemanticProgram, base]
  constructor
  · omega
  · rw [hsize]
    omega

/-- Production V9 form of exact first-hit convergence at an arbitrary reachable activation.
    Acceptance supplies the escape index and one-based active-function layout; the conclusion
    retains both the actual raw prefix index and genuine root reachability of the hit state. -/
theorem v9_verified_successful_private_activation_first_hit
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {steps controller arm : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root start)
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result)
    (hstartStack : start.callStack = spine) (hstartPc : start.pc = arm)
    (hcontroller : controller <
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions.size)
    (hedge : arm ∈
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)).successors.getD
          controller [])
    {lane : Label}
    (_hlane : PrivateControllerLane
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow))
      analysis.localAnalysis controller lane) :
    ∃ elapsed, elapsed < steps ∧
      ActivationContinuationAt (rawSemanticProgram program analysis) root spine
        (analysis.localAnalysis.regions.index.parentAt controller)
        (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
      ReachableFromRoot (rawSemanticProgram program analysis) root
        (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
      ∀ earlier, earlier < elapsed →
        ¬ ActivationContinuationAt (rawSemanticProgram program analysis) root spine
          (analysis.localAnalysis.regions.index.parentAt controller)
          (runPrefix (rawSemanticProgram program analysis) earlier start).state := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hjudgment := v9_occurrence_verifier_sound hverified
  obtain ⟨accepted, _, haccepted, _, hanalyzed, _, _, _⟩ := hjudgment
  have heq : accepted = analysis := by
    rw [hanalysis] at haccepted
    exact Option.some.inj haccepted.symm
  subst accepted
  have htransfer := hanalyzed.2.2.1
  have htransfer' := htransfer
  simp only [transferChecks, Bool.and_eq_true] at htransfer'
  have hindex := htransfer'.1.1.1
  have hcontrollerGraph : controller < (decodedControlGraph base).size := by
    simp [base, ControlGraph.size, decodedControlGraph]
    omega
  have hindexRaw : escapeIndexChecks
      (decodedControlGraph (rawSemanticProgram program analysis))
      analysis.localAnalysis.regions.index = true := by
    rw [decodedControlGraph_rawSemanticProgram]
    exact hindex
  have hcontrollerRaw : controller <
      (decodedControlGraph (rawSemanticProgram program analysis)).size := by
    rw [decodedControlGraph_rawSemanticProgram]
    exact hcontrollerGraph
  have hedgeRaw : arm ∈
      (decodedControlGraph (rawSemanticProgram program analysis)).successors.getD controller [] := by
    rw [decodedControlGraph_rawSemanticProgram]
    exact hedge
  obtain ⟨hactivePositive, hactiveBound⟩ :=
    analyzed_active_function_bounds hanalysis hexecution.start_active
  have hactivePositive' : 0 < (activeFunctionId root spine).toNat := by
    simpa [hstartStack] using hactivePositive
  have hactiveBound' : (activeFunctionId root spine).toNat ≤
      (rawSemanticProgram program analysis).functions.size := by
    simpa [hstartStack] using hactiveBound
  obtain ⟨elapsed, helapsed, hhit, hfirst⟩ :=
    successful_execution_first_continuation_hit hexecution hstartStack hstartPc
      hactivePositive' hactiveBound' hindexRaw hcontrollerRaw hedgeRaw
  exact ⟨elapsed, helapsed, hhit, reachableFromRoot_runPrefix_state hreachable elapsed, hfirst⟩

/-- A raw step at a decoded non-release instruction contributes no Public release observation.
    This closes the small operational gap between the instruction classification returned by the
    region segment theorem and the occurrence-indexed release cursor used by composition. -/
theorem publicReleaseTrace_step_nonrelease
    (machine : SemanticProgram) (state : State) (instruction : Instruction)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (hrelease : instruction.op ≠ .release)
    (hreleaseCT : instruction.op ≠ .releaseCT) :
    publicReleaseTrace machine (step machine state).events = [] := by
  have hinstruction := publicReleaseTrace_instruction_nonrelease
    machine state instruction hrelease hreleaseCT
  unfold step
  by_cases hdone : state.halted || state.trapped
  · simp only [hdone, if_true]
    rfl
  · rw [if_neg hdone, hlookup]
    generalize hop : instruction.op = operation at *
    cases operation
    all_goals simp only [hop]
    case call =>
      unfold callStep
      split
      · simp [publicReleaseTrace, ReleaseSynchronization.releaseTrace,
          Semantic.releaseEvents, EventKind.eqb]
      · dsimp only
        split
        · simp [publicReleaseTrace, ReleaseSynchronization.releaseTrace,
            Semantic.releaseEvents, EventKind.eqb]
        · rfl
    case closure =>
      unfold callStep
      split
      · simp [publicReleaseTrace, ReleaseSynchronization.releaseTrace,
          Semantic.releaseEvents, EventKind.eqb]
      · dsimp only
        split
        · simp [publicReleaseTrace, ReleaseSynchronization.releaseTrace,
            Semantic.releaseEvents, EventKind.eqb]
        · rfl
    case output =>
      cases hstack : state.callStack with
      | nil => simpa [hstack, hop] using hinstruction
      | cons frame rest =>
          simp only
          split <;>
            simp [publicReleaseTrace, ReleaseSynchronization.releaseTrace,
              Semantic.releaseEvents, EventKind.eqb]
    case release => exact (hrelease rfl).elim
    case releaseCT => exact (hreleaseCT rfl).elim
    case ffi => simpa [hop] using hinstruction
    case actorBoundary => simpa [hop] using hinstruction
    case effect => simpa [hop] using hinstruction
    case abortiveEffect => simpa [hop] using hinstruction
    case stateRead => rfl
    case stateWrite => simpa [hop] using hinstruction
    all_goals simpa [ordinaryStep, hop] using hinstruction

private theorem eq_public_of_flowsTo_public {label : Label}
    (hflow : label.flowsTo .pub = true) : label = .pub := by
  cases label <;> simp_all [Label.flowsTo, Label.rank]

/-- At the current activation, the verifier's local occurrence is an actual lower bound of the
    raised raw block label.  Hence a private activation anchor makes the raw step boundary-silent
    without reading a runtime-controlled label. -/
theorem current_private_anchor_has_no_public_boundary_observation
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    {root : UInt32} {spine : List CallFrame} {anchor : Nat} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hnextActive : ActiveState (rawSemanticProgram program analysis) root
      (step (rawSemanticProgram program analysis) state).state)
    (hstack : state.callStack = spine)
    (hanchor : ActivationAnchor spine anchor state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub) :
    publicBoundaryTrace (step (rawSemanticProgram program analysis) state).events = [] := by
  have hanchorPc : anchor = state.pc := hanchor.current_injective hstack
  by_cases houtput : instruction.op = .output
  · cases spine with
    | nil =>
        have hhalted :
            (step (rawSemanticProgram program analysis) state).state.halted = true := by
          unfold step
          simp [hactive.notHalted, hactive.notTrapped, hlookup, houtput, hstack]
        have hnextNotHalted := hnextActive.notHalted
        rw [hhalted] at hnextNotHalted
        contradiction
    | cons frame rest =>
        have hnonempty : state.callStack ≠ [] := by
          rw [hstack]
          simp
        unfold step
        simp only [hactive.notHalted, hactive.notTrapped, Bool.false_or,
          Bool.false_eq_true, if_false, hlookup, houtput]
        cases hframes : state.callStack with
        | nil => exact False.elim (hnonempty hframes)
        | cons returned rest =>
            simp only
            split <;> simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]
  · have hflow := local_occurrence_flows_to_raw_block_of_lookup hlookup houtput
    have hrawNonpublic : instruction.blockLabel ≠ .pub := by
      intro hpublic
      have hlocalPublic : localOccurrenceAt analysis.localAnalysis.frontiers state.pc = .pub :=
        eq_public_of_flowsTo_public (by simpa [hpublic] using hflow)
      exact hnonpublic (by simpa [hanchorPc] using hlocalPublic)
    exact nonpublic_step_has_no_public_boundary_observation
      (rawSemanticProgram program analysis) state instruction hlookup hrawNonpublic

/-- A nested output is an internal return, not a Public boundary event.  Its occurrence-raised
    raw block may be Public because it also serves an externally callable root; the live stack,
    rather than that label, is the load-bearing discriminator. -/
theorem descendant_output_has_no_public_boundary_observation
    {machine : SemanticProgram} {root : UInt32} {state : State}
    {instruction : Instruction} {inner spine : List CallFrame} {outer : CallFrame}
    (hactive : ActiveState machine root state)
    (hstack : state.callStack = inner ++ outer :: spine)
    (hlookup : machine.instructions[state.pc]? = some instruction)
    (houtput : instruction.op = .output) :
    publicBoundaryTrace (step machine state).events = [] := by
  have hnonempty : state.callStack ≠ [] := by
    rw [hstack]
    simp
  unfold step
  simp only [hactive.notHalted, hactive.notTrapped, Bool.false_or, Bool.false_eq_true,
    if_false, hlookup, houtput]
  cases hframes : state.callStack with
  | nil => exact False.elim (hnonempty hframes)
  | cons frame rest =>
      simp only
      split <;> simp [publicBoundaryTrace, publicBoundaryObservation?, EventKind.eqb]

/-- The activation anchor, rather than the current raw block label, is the stable classifier for
    a private stuttering segment.  In the current activation this is the local occurrence.  In a
    descendant activation it flows through the exact suspended call and every coherent nested
    frame into the current invocation summary.  Internal outputs are handled operationally as
    returns, since their root-return raise may legitimately make their raw label Public. -/
theorem private_activation_anchor_has_no_public_boundary_observation
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {anchor : Nat} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hnextActive : ActiveState (rawSemanticProgram program analysis) root
      (step (rawSemanticProgram program analysis) state).state)
    (hanchor : ActivationAnchor spine anchor state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub) :
    publicBoundaryTrace (step (rawSemanticProgram program analysis) state).events = [] := by
  cases hanchor with
  | current hstack =>
      exact current_private_anchor_has_no_public_boundary_observation hactive hnextActive hstack
        (.current hstack) hlookup hnonpublic
  | descendant inner outer hstack =>
      by_cases houtput : instruction.op = .output
      · exact descendant_output_has_no_public_boundary_observation hactive hstack hlookup houtput
      · have hchain := hactive.frameChain
        rw [hstack] at hchain
        obtain ⟨houter, hinner⟩ := frameChain_split_activation hchain
        have hanchorToOuter := coherent_frame_local_occurrence_flows_to_callee hanalysis houter
        have houterToActive := frameChain_root_occurrence_flows_to_active hanalysis hinner
        have hanchorToActive := labelFlows_trans hanchorToOuter houterToActive
        obtain ⟨current, hcurrentLookup, hcurrentFunction⟩ := hactive.currentInstruction
        have hcurrentEq : current = instruction := by
          rw [hlookup] at hcurrentLookup
          exact Option.some.inj hcurrentLookup.symm
        subst current
        have hactiveEq : activeFunctionId root state.callStack =
            activeFunctionId outer.calleeId inner := by
          rw [hstack]
          exact activeFunctionId_append_outer root inner outer spine
        have hactiveToBlock :=
          invocation_occurrence_flows_to_raw_block_of_lookup hlookup houtput
        have hanchorToBlock :
            (localOccurrenceAt analysis.localAnalysis.frontiers (outer.returnPc - 1)).flowsTo
              instruction.blockLabel = true := by
          apply labelFlows_trans hanchorToActive
          rw [← hactiveEq, ← hcurrentFunction]
          exact hactiveToBlock
        have hrawNonpublic : instruction.blockLabel ≠ .pub := by
          intro hpublic
          have hanchorPublic :
              localOccurrenceAt analysis.localAnalysis.frontiers (outer.returnPc - 1) = .pub :=
            eq_public_of_flowsTo_public (by simpa [hpublic] using hanchorToBlock)
          exact hnonpublic hanchorPublic
        exact nonpublic_step_has_no_public_boundary_observation
          (rawSemanticProgram program analysis) state instruction hlookup hrawNonpublic

/-- Invocation-private execution is boundary silent even when it was entered directly from a
    Public call site rather than from an intraprocedural private controller.  The proof uses the
    verifier's invocation label and the actual coherent frames above `spine`; closure targets are
    covered by the checked dynamic-target fan-out. -/
theorem private_invocation_activation_has_no_public_boundary_observation
    {program : V9.Program} {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {spine : List CallFrame} {state : State}
    {instruction : Instruction}
    (hactive : ActiveState (rawSemanticProgram program analysis) root state)
    (hspine : spine ≠ []) (hlive : ActivationLive spine state)
    (hlookup : (rawSemanticProgram program analysis).instructions[state.pc]? =
      some instruction)
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub) :
    publicBoundaryTrace (step (rawSemanticProgram program analysis) state).events = [] := by
  obtain ⟨privateFrames, hstack⟩ := hlive
  by_cases houtput : instruction.op = .output
  · rcases List.exists_cons_of_ne_nil hspine with ⟨outer, rest, rfl⟩
    exact descendant_output_has_no_public_boundary_observation hactive hstack hlookup houtput
  · have hchain := hactive.frameChain
    rw [hstack] at hchain
    have hprefixChain := frameChain_prefix_above_suffix hchain
    have hinvocationToActive := frameChain_root_occurrence_flows_to_active hanalysis hprefixChain
    obtain ⟨current, hcurrentLookup, hcurrentFunction⟩ := hactive.currentInstruction
    have hcurrentEq : current = instruction := by
      rw [hlookup] at hcurrentLookup
      exact Option.some.inj hcurrentLookup.symm
    subst current
    have hactiveEq : activeFunctionId root state.callStack =
        activeFunctionId (activeFunctionId root spine) privateFrames := by
      rw [hstack]
      exact activeFunctionId_append_suffix root privateFrames spine
    have hactiveToBlock :=
      invocation_occurrence_flows_to_raw_block_of_lookup hlookup houtput
    have hrootToBlock : (labelAt analysis.labels (activeFunctionId root spine)).flowsTo
        instruction.blockLabel = true := by
      apply labelFlows_trans hinvocationToActive
      rw [← hactiveEq, ← hcurrentFunction]
      exact hactiveToBlock
    have hrawNonpublic : instruction.blockLabel ≠ .pub := by
      intro hpublic
      have hrootPublic : labelAt analysis.labels (activeFunctionId root spine) = .pub :=
        eq_public_of_flowsTo_public (by simpa [hpublic] using hrootToBlock)
      exact hnonpublic hrootPublic
    exact nonpublic_step_has_no_public_boundary_observation
      (rawSemanticProgram program analysis) state instruction hlookup hrawNonpublic

/-- Exact successful segment for an invocation-private callee, including the case where a Public
    call/closure selected a private invocation.  The endpoint is the actual raw return: its stack
    is the caller tail and its pc is the coherent frame continuation.  Every strict prefix is a
    genuine reachable active state and emits no Public boundary observation.  Releases are kept
    explicit, because a legal release inside the invocation may change the Public projection. -/
theorem v9_verified_successful_private_invocation_segment
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {steps : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root start)
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result)
    (hstartStack : start.callStack = spine) (hspine : spine ≠ [])
    (hnonpublic : labelAt analysis.labels (activeFunctionId root spine) ≠ .pub) :
    ∃ exitStep frame rest output,
      0 < exitStep ∧ exitStep < steps ∧ spine = frame :: rest ∧
        (runPrefix (rawSemanticProgram program analysis) (exitStep - 1) start).state.callStack =
          spine ∧
        (rawSemanticProgram program analysis).instructions[
          (runPrefix (rawSemanticProgram program analysis) (exitStep - 1) start).state.pc]? =
            some output ∧
        output.functionId = activeFunctionId root spine ∧ output.op = .output ∧
        (runPrefix (rawSemanticProgram program analysis) exitStep start).state.callStack = rest ∧
        (runPrefix (rawSemanticProgram program analysis) exitStep start).state.pc =
          frame.returnPc ∧
        ReachableFromRoot (rawSemanticProgram program analysis) root
          (runPrefix (rawSemanticProgram program analysis) exitStep start).state ∧
        ∀ earlier, earlier < exitStep →
          ReachableFromRoot (rawSemanticProgram program analysis) root
              (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
            ActiveState (rawSemanticProgram program analysis) root
              (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
            ActivationLive spine
              (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
            ∃ instruction,
              (rawSemanticProgram program analysis).instructions[
                (runPrefix (rawSemanticProgram program analysis) earlier start).state.pc]? =
                  some instruction ∧
              publicBoundaryTrace
                  (step (rawSemanticProgram program analysis)
                    (runPrefix (rawSemanticProgram program analysis) earlier start).state).events =
                [] ∧
              ((instruction.op = .release ∨ instruction.op = .releaseCT) ∨
                (instruction.op ≠ .release ∧ instruction.op ≠ .releaseCT ∧
                  publicReleaseTrace (rawSemanticProgram program analysis)
                    (step (rawSemanticProgram program analysis)
                      (runPrefix (rawSemanticProgram program analysis) earlier start).state).events =
                    [])) := by
  classical
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  obtain ⟨accepted, _, haccepted, _, _, _, _, _⟩ := hjudgment
  have heq : accepted = analysis := by
    rw [hanalysis] at haccepted
    exact Option.some.inj haccepted.symm
  subst accepted
  obtain ⟨exitStep, output, hexitPositive, hexitBound, hlive,
    hbeforeStack, hlookup, hfunction, houtput⟩ :=
    successful_execution_first_activation_exit hexecution hstartStack hspine
  rcases List.exists_cons_of_ne_nil hspine with ⟨frame, rest, hspineEq⟩
  let before := (runPrefix machine (exitStep - 1) start).state
  let after := (runPrefix machine exitStep start).state
  have hnextState : after = (step machine before).state := by
    have hadd := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add machine (exitStep - 1) 1 start)
    have hsum : exitStep - 1 + 1 = exitStep := by omega
    rw [hsum] at hadd
    simpa only [runPrefix, before, after] using hadd
  have hbeforeActive := hexecution.reached_active (elapsed := exitStep - 1) (by omega)
  have hafterActiveRaw := hexecution.reached_active (elapsed := exitStep) hexitBound
  have hafterActive : ActiveState machine root (step machine before).state := by
    rw [← hnextState]
    exact hafterActiveRaw
  have htransition := live_step_stack_transition hlookup hbeforeActive.notHalted
    hbeforeActive.notTrapped hafterActive.notHalted hafterActive.notTrapped
  cases htransition with
  | same hsame _ _ hnotReturn => exact False.elim (hnotReturn houtput)
  | push pushed hpush hreturnPc hoperation =>
      rcases hoperation with hcall | hclosure
      · cases houtput.symm.trans hcall
      · cases houtput.symm.trans hclosure
  | pop actualFrame actualRest hbeforePop hafterStack hafterPc hoperation =>
      have hbeforeCons : before.callStack = frame :: rest := by
        simpa [before] using hbeforeStack.trans hspineEq
      have hcons : actualFrame :: actualRest = frame :: rest := by
        exact hbeforePop.symm.trans hbeforeCons
      have hframeEq : actualFrame = frame := List.cons.inj hcons |>.1
      have hrestEq : actualRest = rest := List.cons.inj hcons |>.2
      refine ⟨exitStep, frame, rest, output, hexitPositive, hexitBound, hspineEq,
        by simpa [before] using hbeforeStack, by simpa [machine, before] using hlookup,
        hfunction, houtput, ?_, ?_, reachableFromRoot_runPrefix_state hreachable exitStep, ?_⟩
      · change after.callStack = rest
        rw [hnextState]
        exact hafterStack.trans hrestEq
      · change after.pc = frame.returnPc
        rw [hnextState]
        simpa [hframeEq] using hafterPc
      · intro earlier hearlier
        have hearlierSteps : earlier < steps := by omega
        have hearlierActive := hexecution.reached_active (elapsed := earlier) hearlierSteps
        have hearlierLive := hlive earlier hearlier
        obtain ⟨instruction, hinstruction, _⟩ := hearlierActive.currentInstruction
        have hboundary := private_invocation_activation_has_no_public_boundary_observation
          hanalysis hearlierActive hspine hearlierLive hinstruction hnonpublic
        have hopClass : ((instruction.op = .release ∨ instruction.op = .releaseCT) ∨
            (instruction.op ≠ .release ∧ instruction.op ≠ .releaseCT ∧
              publicReleaseTrace machine
                (step machine (runPrefix machine earlier start).state).events = [])) := by
          by_cases hrelease : instruction.op = .release
          · exact Or.inl (Or.inl hrelease)
          · by_cases hreleaseCT : instruction.op = .releaseCT
            · exact Or.inl (Or.inr hreleaseCT)
            · exact Or.inr ⟨hrelease, hreleaseCT,
                publicReleaseTrace_step_nonrelease machine
                  (runPrefix machine earlier start).state instruction hinstruction
                  hrelease hreleaseCT⟩
        exact ⟨reachableFromRoot_runPrefix_state hreachable earlier, hearlierActive,
          hearlierLive, instruction, hinstruction, hboundary, hopClass⟩

/-- Strong private-segment form of the V9 first-hit theorem.  Every strict raw prefix carries an
    exact activation anchor whose verifier-derived local occurrence is non-Public.  Descendant
    calls (including closure calls and recursion) are classified at their genuine caller anchor;
    this deliberately avoids the false claim that a nested output's root-return-raised raw
    `blockLabel` is private. -/
theorem v9_verified_successful_private_activation_segment
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {steps controller arm : Nat} {start : State} {result : StepResult}
    {spine : List CallFrame}
    (hreachable : ReachableFromRoot (rawSemanticProgram program analysis) root start)
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result)
    (hstartStack : start.callStack = spine) (hstartPc : start.pc = arm)
    (hcontroller : controller <
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions.size)
    (hedge : arm ∈
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)).successors.getD
          controller [])
    {lane : Label}
    (hlane : PrivateControllerLane
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow))
      analysis.localAnalysis controller lane) :
    ∃ elapsed, elapsed < steps ∧
      ActivationContinuationAt (rawSemanticProgram program analysis) root spine
        (analysis.localAnalysis.regions.index.parentAt controller)
        (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
      ReachableFromRoot (rawSemanticProgram program analysis) root
        (runPrefix (rawSemanticProgram program analysis) elapsed start).state ∧
      (analysis.localAnalysis.regions.index.parentAt controller =
          functionReturn (rawSemanticProgram program analysis)
            (activeFunctionId root spine) →
        ∃ instruction,
          (rawSemanticProgram program analysis).instructions[
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc]? =
            some instruction ∧
          localOccurrenceAt analysis.localAnalysis.frontiers
              (runPrefix (rawSemanticProgram program analysis) elapsed start).state.pc ≠ .pub) ∧
      ∀ earlier, earlier < elapsed →
        ¬ ActivationContinuationAt (rawSemanticProgram program analysis) root spine
            (analysis.localAnalysis.regions.index.parentAt controller)
            (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
          ReachableFromRoot (rawSemanticProgram program analysis) root
            (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
          ActiveState (rawSemanticProgram program analysis) root
            (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
          ∃ anchor instruction,
            ActivationAnchor spine anchor
                (runPrefix (rawSemanticProgram program analysis) earlier start).state ∧
              (rawSemanticProgram program analysis).instructions[
                  (runPrefix (rawSemanticProgram program analysis) earlier start).state.pc]? =
                some instruction ∧
              instruction.functionId = activeFunctionId root
                (runPrefix (rawSemanticProgram program analysis) earlier start).state.callStack ∧
              localOccurrenceAt analysis.localAnalysis.frontiers anchor ≠ .pub ∧
              publicBoundaryTrace
                  (step (rawSemanticProgram program analysis)
                    (runPrefix (rawSemanticProgram program analysis) earlier start).state).events =
                [] ∧
              ((instruction.op = .release ∨ instruction.op = .releaseCT) ∨
                (instruction.op ≠ .release ∧ instruction.op ≠ .releaseCT ∧
                  publicReleaseTrace (rawSemanticProgram program analysis)
                    (step (rawSemanticProgram program analysis)
                      (runPrefix (rawSemanticProgram program analysis) earlier start).state).events =
                    [])) := by
  classical
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  let machine := rawSemanticProgram program analysis
  have hjudgment := v9_occurrence_verifier_sound hverified
  obtain ⟨accepted, _, haccepted, _, hanalyzed, _, _, _⟩ := hjudgment
  have heq : accepted = analysis := by
    rw [hanalysis] at haccepted
    exact Option.some.inj haccepted.symm
  subst accepted
  have htransfer := hanalyzed.2.2.1
  have htransfer' := htransfer
  simp only [transferChecks, Bool.and_eq_true] at htransfer'
  have hindex := htransfer'.1.1.1
  have hcontrollerGraph : controller < (decodedControlGraph base).size := by
    simp [base, ControlGraph.size, decodedControlGraph]
    omega
  obtain ⟨hactivePositive, hactiveBound⟩ :=
    analyzed_active_function_bounds hanalysis hexecution.start_active
  have hactivePositive' : 0 < (activeFunctionId root spine).toNat := by
    simpa [hstartStack] using hactivePositive
  have hactiveBound' : (activeFunctionId root spine).toNat ≤ machine.functions.size := by
    simpa [machine, hstartStack] using hactiveBound
  obtain ⟨fuel, finish, exit, anchors, compressed, hfuel, hfinish, hrawPath,
    hcontrol, hsublist, hcover, hsuccessful, hreturnAt⟩ :=
    successful_activation_control_witness hexecution hstartStack
      hactivePositive' hactiveBound'
  have hsuccessfulBase := hsuccessful
  rw [show decodedControlGraph machine = decodedControlGraph base by
    simpa [machine, base] using decodedControlGraph_rawSemanticProgram program analysis]
      at hsuccessfulBase
  rw [hstartPc] at hsuccessfulBase
  have hhit := checked_controller_parent_hits_successful_path hindex hcontrollerGraph hedge
    hsuccessfulBase
  have hmember : analysis.localAnalysis.regions.index.parentAt controller ∈ compressed ∨
      analysis.localAnalysis.regions.index.parentAt controller =
        functionReturn machine (activeFunctionId root spine) := by
    simpa only [List.mem_append, List.mem_singleton] using hhit
  have hexists : ∃ elapsed, elapsed ≤ fuel ∧
      ActivationContinuationAt machine root spine
        (analysis.localAnalysis.regions.index.parentAt controller)
        (runPrefix machine elapsed start).state := by
    rcases hmember with hcompressed | hreturn
    · have hanchors : analysis.localAnalysis.regions.index.parentAt controller ∈ anchors :=
        hsublist.subset hcompressed
      obtain ⟨elapsed, helapsed, hanchor, _⟩ := hrawPath.first_anchor_hit hanchors
      exact ⟨elapsed, helapsed, Or.inl hanchor⟩
    · refine ⟨fuel, le_rfl, ?_⟩
      rw [hfinish] at hreturnAt
      simpa [hreturn] using hreturnAt
  let elapsed := Nat.find hexists
  have hspec := Nat.find_spec hexists
  have helapsedSteps : elapsed < steps := by omega
  have hendpointPrivate :
      analysis.localAnalysis.regions.index.parentAt controller =
          functionReturn machine (activeFunctionId root spine) →
        ∃ instruction,
          machine.instructions[(runPrefix machine elapsed start).state.pc]? =
            some instruction ∧
          localOccurrenceAt analysis.localAnalysis.frontiers
              (runPrefix machine elapsed start).state.pc ≠ .pub := by
    intro hparentReturn
    have hparentReturn' : analysis.localAnalysis.regions.index.parentAt controller =
        functionReturn machine (activeFunctionId root spine) := by
      simpa [machine] using hparentReturn
    have hendStack : (runPrefix machine elapsed start).state.callStack = spine := by
      rcases hspec.2 with hanchor | hsynthetic
      · have hanchorBound := active_activationAnchor_lt_instructions
          (hexecution.reached_active helapsedSteps) hanchor
        have hanchorBound' :
            analysis.localAnalysis.regions.index.parentAt controller <
              machine.instructions.size := by
          simpa [machine] using hanchorBound
        rw [hparentReturn', functionReturn] at hanchorBound'
        omega
      · exact hsynthetic.2.1
    obtain ⟨target, prefixTrace, hprefixRaw⟩ := hrawPath.take elapsed hspec.1
    have htargetAnchor := hprefixRaw.endAnchor
    have htargetPc : target = (runPrefix machine elapsed start).state.pc :=
      htargetAnchor.current_injective hendStack
    obtain ⟨prefixControl, hprefixPath, hprefixSublist, _⟩ :=
      hprefixRaw.toStutteringControlPath.toControlPath_cover
    have hprefixBase := hprefixPath
    rw [show decodedControlGraph machine = decodedControlGraph base by
      simpa [machine, base] using decodedControlGraph_rawSemanticProgram program analysis]
        at hprefixBase
    rw [hstartPc] at hprefixBase
    have helapsedTrace : elapsed < anchors.length := by
      rw [hrawPath.trace_length]
      omega
    have hfullAnchor := hrawPath.get_anchor elapsed helapsedTrace
    have htargetEq : target = anchors.get ⟨elapsed, helapsedTrace⟩ :=
      htargetAnchor.unique hfullAnchor
    have htargetAnchors : target ∈ anchors := by
      rw [htargetEq]
      exact List.getElem_mem helapsedTrace
    have htargetCompressed : target ∈ compressed := hcover target htargetAnchors
    have htargetSuccessful : ∃ suffix,
        SuccessfulPath (decodedControlGraph base) target suffix := by
      apply successfulPath_suffix_of_mem hsuccessfulBase
      exact List.mem_append_left _ htargetCompressed
    have htargetBound : target < (decodedControlGraph base).size :=
      checked_successful_path_start_bound hindex htargetSuccessful.choose_spec
    have hparentAvoid : analysis.localAnalysis.regions.index.parentAt controller ∉
        prefixControl := by
      intro hparentMember
      have hparentRaw : analysis.localAnalysis.regions.index.parentAt controller ∈
          prefixTrace := hprefixSublist.subset hparentMember
      obtain ⟨hitAt, hhitAtBound, hhitAnchor, _⟩ :=
        hprefixRaw.first_anchor_hit hparentRaw
      have hhitActive := hexecution.reached_active (elapsed := hitAt) (by omega)
      have hhitBound := active_activationAnchor_lt_instructions hhitActive hhitAnchor
      have hhitBound' : analysis.localAnalysis.regions.index.parentAt controller <
          machine.instructions.size := by
        simpa [machine] using hhitBound
      rw [hparentReturn', functionReturn] at hhitBound'
      omega
    have hnonpublic := checked_private_controller_prefix_is_nonpublic htransfer hlane
      hcontrollerGraph hedge hprefixBase htargetBound htargetSuccessful hparentAvoid
    obtain ⟨instruction, hlookup, _⟩ :=
      (hexecution.reached_active helapsedSteps).currentInstruction
    exact ⟨instruction, hlookup, by simpa [htargetPc] using hnonpublic⟩
  refine ⟨elapsed, helapsedSteps, hspec.2,
    reachableFromRoot_runPrefix_state hreachable elapsed, hendpointPrivate, ?_⟩
  intro earlier hearlier
  have hearlierFuel : earlier ≤ fuel := by omega
  have hfirst : ¬ ActivationContinuationAt machine root spine
      (analysis.localAnalysis.regions.index.parentAt controller)
      (runPrefix machine earlier start).state := by
    intro hearlierHit
    exact Nat.find_min hexists hearlier ⟨hearlierFuel, hearlierHit⟩
  obtain ⟨target, prefixTrace, hprefixRaw⟩ := hrawPath.take earlier hearlierFuel
  have htargetAnchor := hprefixRaw.endAnchor
  obtain ⟨prefixControl, hprefixPath, hprefixSublist, _⟩ :=
    hprefixRaw.toStutteringControlPath.toControlPath_cover
  have hprefixBase := hprefixPath
  rw [show decodedControlGraph machine = decodedControlGraph base by
    simpa [machine, base] using decodedControlGraph_rawSemanticProgram program analysis]
      at hprefixBase
  rw [hstartPc] at hprefixBase
  have hearlierTrace : earlier < anchors.length := by
    rw [hrawPath.trace_length]
    omega
  have hfullAnchor := hrawPath.get_anchor earlier hearlierTrace
  have htargetEq : target = anchors.get ⟨earlier, hearlierTrace⟩ :=
    htargetAnchor.unique hfullAnchor
  have htargetAnchors : target ∈ anchors := by
    rw [htargetEq]
    exact List.getElem_mem hearlierTrace
  have htargetCompressed : target ∈ compressed := hcover target htargetAnchors
  have htargetSuccessful : ∃ suffix,
      SuccessfulPath (decodedControlGraph base) target suffix := by
    apply successfulPath_suffix_of_mem hsuccessfulBase
    exact List.mem_append_left _ htargetCompressed
  have htargetBound : target < (decodedControlGraph base).size :=
    checked_successful_path_start_bound hindex htargetSuccessful.choose_spec
  have hparentAvoid : analysis.localAnalysis.regions.index.parentAt controller ∉
      prefixControl := by
    intro hparent
    have hparentRaw : analysis.localAnalysis.regions.index.parentAt controller ∈ prefixTrace :=
      hprefixSublist.subset hparent
    obtain ⟨hitAt, hhitAtBound, hhitAnchor, _⟩ :=
      hprefixRaw.first_anchor_hit hparentRaw
    exact Nat.find_min hexists (by omega) ⟨by omega, Or.inl hhitAnchor⟩
  have hnonpublic := checked_private_controller_prefix_is_nonpublic htransfer hlane
    hcontrollerGraph hedge hprefixBase htargetBound htargetSuccessful hparentAvoid
  have hactive := hexecution.reached_active (elapsed := earlier) (by omega)
  obtain ⟨instruction, hlookup, hfunction⟩ := hactive.currentInstruction
  have hopClass : ((instruction.op = .release ∨ instruction.op = .releaseCT) ∨
      (instruction.op ≠ .release ∧ instruction.op ≠ .releaseCT ∧
        publicReleaseTrace machine
          (step machine (runPrefix machine earlier start).state).events = [])) := by
    by_cases hrelease : instruction.op = .release
    · exact Or.inl (Or.inl hrelease)
    · by_cases hreleaseCT : instruction.op = .releaseCT
      · exact Or.inl (Or.inr hreleaseCT)
      · exact Or.inr ⟨hrelease, hreleaseCT,
          publicReleaseTrace_step_nonrelease machine
            (runPrefix machine earlier start).state instruction hlookup hrelease hreleaseCT⟩
  have hnextActive := hexecution.reached_active (elapsed := earlier + 1) (by omega)
  have hstepState :
      (runPrefix machine (earlier + 1) start).state =
        (step machine (runPrefix machine earlier start).state).state := by
    have hdecompose := congrArg StepResult.state
      (ReleaseSynchronization.runPrefix_add machine earlier 1 start)
    simpa [runPrefix] using hdecompose
  rw [hstepState] at hnextActive
  have hboundary := private_activation_anchor_has_no_public_boundary_observation hanalysis
    hactive hnextActive htargetAnchor hlookup hnonpublic
  exact ⟨hfirst, reachableFromRoot_runPrefix_state hreachable earlier, hactive,
    target, instruction, htargetAnchor, hlookup, hfunction, hnonpublic, hboundary, hopClass⟩

/-! ## Context-split output counterexample -/

private def contextSplitOutput : Instruction :=
  { op := .output, id := 1, functionId := 2, blockId := 1, destination := 0
    firstOperand := 0, operandCount := 1, target := 0, alternate := 0, merge := 0
    blockLabel := .pub, resultLabel := .pub, aux := 0 }

private def contextSplitMachine : SemanticProgram :=
  { functions := #[]
    instructions := #[contextSplitOutput]
    operands := #[{ owner := 1, position := 0, value := 0, kind := 0 }]
    valueLabels := #[.pub] }

private def contextSplitFrame : CallFrame :=
  { returnPc := 1, destination := 0, calleeId := 2, returnLabel := .pub
    savedParameters := [] }

private def contextSplitState : State :=
  { pc := 0, values := #[⟨.pub, 7⟩], aggregates := #[], capabilityBalances := #[]
    callStack := [contextSplitFrame] }

/-- Kernel-checked counterexample to the tempting raw-label invariant: a nested return may retain
    a Public root-return label while producing no Public boundary observation at all.  Region
    composition must use the activation/effective occurrence and the live call context. -/
theorem nested_public_output_is_internal_boundary_silent :
    contextSplitOutput.blockLabel = .pub ∧ contextSplitState.callStack ≠ [] ∧
      publicBoundaryTrace (step contextSplitMachine contextSplitState).events = [] := by
  decide +kernel

/-- Load-bearing production bridge for a root activation.  V9 acceptance supplies the exact
    checked escape index; the raw execution supplies a real finite successful path, including
    balanced direct calls, closure calls, recursion, and returns.  Therefore the chosen arm hits
    the verifier-derived continuation.  The universal second conjunct states the no-intervening-
    Public fact for every live decoded prefix before that hit, for either ordinary private lane.

    This theorem uses the execution's own `steps`; no common relational fuel appears. -/
theorem v9_verified_successful_private_root_region_reaches_continuation
    {program : V9.Program}
    (hverified : V9.OccurrenceKernel.verifyProgram program = none)
    {analysis : V9.OccurrenceDataflowInvocation.Analysis}
    (hanalysis : V9.OccurrenceDataflowInvocation.analyze? program = some analysis)
    {root : UInt32} {steps controller arm : Nat} {start : State} {result : StepResult}
    (hexecution : SuccessfulExecution (rawSemanticProgram program analysis)
      root steps start result)
    (hstartStack : start.callStack = []) (hstartPc : start.pc = arm)
    (hcontroller : controller <
      (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow).instructions.size)
    (hedge : arm ∈
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)).successors.getD
          controller [])
    {lane : Label}
    (hlane : PrivateControllerLane
      (decodedControlGraph
        (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow))
      analysis.localAnalysis controller lane) :
    ∃ trace,
      SuccessfulPath
          (decodedControlGraph
            (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)) arm trace ∧
        analysis.localAnalysis.regions.index.parentAt controller ∈ trace ∧
        ∀ {target : Nat} {pathTrace : List Nat},
          ControlPath
              (decodedControlGraph
                (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow))
              arm target pathTrace →
          target <
              (decodedControlGraph
                (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow)).size →
          (∃ completionTrace,
            SuccessfulPath
              (decodedControlGraph
                (V9.OccurrenceDataflow.semanticProgram program analysis.dataflow))
              target completionTrace) →
          analysis.localAnalysis.regions.index.parentAt controller ∉ pathTrace →
          localOccurrenceAt analysis.localAnalysis.frontiers target ≠ .pub := by
  let base := V9.OccurrenceDataflow.semanticProgram program analysis.dataflow
  have hjudgment := v9_occurrence_verifier_sound hverified
  obtain ⟨accepted, _, haccepted, _, hanalyzed, _, _, _⟩ := hjudgment
  have heq : accepted = analysis := by
    rw [hanalysis] at haccepted
    exact Option.some.inj haccepted.symm
  subst accepted
  have htransfer := hanalyzed.2.2.1
  have htransfer' := htransfer
  simp only [transferChecks, Bool.and_eq_true] at htransfer'
  have hindex := htransfer'.1.1.1
  obtain ⟨hrootPositive, hrootBound⟩ := analyzed_successful_root_bounds hanalysis hexecution
  obtain ⟨trace, hpath⟩ := successful_root_execution_has_successful_control_path
    hexecution hstartStack hrootPositive hrootBound
  rw [decodedControlGraph_rawSemanticProgram] at hpath
  rw [hstartPc] at hpath
  have hcontrollerGraph : controller < (decodedControlGraph base).size := by
    simp [base, ControlGraph.size, decodedControlGraph]
    omega
  have hhit := checked_controller_parent_hits_successful_path hindex hcontrollerGraph hedge hpath
  refine ⟨trace, hpath, hhit, ?_⟩
  intro target pathTrace hprefix htarget hcompletion havoid
  exact checked_private_controller_prefix_is_nonpublic htransfer hlane hcontrollerGraph hedge
    hprefix htarget hcompletion havoid

end LambdaSigil.Combined.Semantic.PublicRegionConvergence
