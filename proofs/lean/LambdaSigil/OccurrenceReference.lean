import LambdaSigil.CombinedKernel

/-!
# Occurrence-control reference classifier

This is a deliberately small, executable specification for the v9 control-dependence work. It is
NOT the production verifier: repeated reachability and fixed-point queries are deliberately slow,
and the inputs here are normalized CFGs rather than decoded CSIR. The bounded production region index
must be checked against this oracle, not replaced by it. In particular, the selector labels below
are parameters of the reference problem; this module does not claim to derive semantic labels.

Successful-path postdominance ignores paths that trap or diverge. A controller depends on itself
when one of its successors must return to it: this is the important loop-header occurrence case.
Neither numeric block ordering nor a supplied merge marker participates in the calculation.
Invocation influence is kept separate from return-value contracts: a pure helper is not a Public
action merely because it returns a Public constant. Empty-payload actions still have a sink.
-/

namespace LambdaSigil.Combined.OccurrenceReference

structure Graph where
  successors : Array (List Nat)
  successfulExits : List Nat
  selectors : Array Label
  deriving Repr, Inhabited

def Graph.size (g : Graph) : Nat := g.successors.size

def Graph.wellFormed (g : Graph) : Bool :=
  g.size != 0 && g.selectors.size == g.size &&
    g.successfulExits.all (fun n => n < g.size && (g.successors[n]!).isEmpty) &&
    g.successors.all (fun targets => targets.all (fun n => n < g.size))

/-- An expanded vertex contributes its outgoing edges once. The work budget counts queued edges,
    not only vertices, so duplicate edges and cycles do not silently truncate the search. -/
def visit (g : Graph) (avoid : Option Nat) :
    Nat → List Nat → Array Bool → Array Bool
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | fuel + 1, node :: work, seen =>
      if node ≥ g.size || avoid == some node || seen[node]! then
        visit g avoid fuel work seen
      else
        visit g avoid fuel (g.successors[node]! ++ work) (seen.set! node true)

def reachable (g : Graph) (avoid : Option Nat) (start : Nat) : Array Bool :=
  visit g avoid (1 + g.successors.foldl (fun count edges => count + edges.length) 0)
    [start] (Array.replicate g.size false)

def canSucceed (g : Graph) (avoid : Option Nat) (start : Nat) : Bool :=
  let seen := reachable g avoid start
  g.successfulExits.any (fun exit => seen[exit]!)

/-- Non-vacuous successful-path postdominance. Dead/trapping components cannot manufacture
    continuations merely because they have no successful path. -/
def postdominates (g : Graph) (candidate start : Nat) : Bool :=
  candidate < g.size && canSucceed g none start && !canSucceed g (some candidate) start

def controls (g : Graph) (controller occurrence : Nat) : Bool :=
  controller < g.size && occurrence < g.size &&
    (g.successors[controller]!).length > 1 &&
    (occurrence == controller || !postdominates g occurrence controller) &&
    (g.successors[controller]!).any (postdominates g occurrence)

def localStep (g : Graph) (labels : Array Label) : Array Label :=
  (List.range g.size).toArray.map fun occurrence =>
    (List.range g.size).foldl (fun label controller =>
      if controls g controller occurrence then
        label.lub ((g.selectors.getD controller .pub).lub (labels.getD controller .pub))
      else label) (labels.getD occurrence .pub)

def localIterate (g : Graph) : Nat → Array Label → Array Label
  | 0, labels => labels
  | fuel + 1, labels => localIterate g fuel (localStep g labels)

/-- Control dependence is transitive: a Public selector inside a private arm does not make the
    inner arm's occurrence Public. Keep these labels separate from selector payload labels. -/
def localLabels (g : Graph) : Array Label :=
  localIterate g (3 * g.size) (Array.replicate g.size .pub)

def localClosed (g : Graph) : Bool := localStep g (localLabels g) == localLabels g

def localInfluence (g : Graph) (occurrence : Nat) : Label :=
  (localLabels g).getD occurrence .pub

structure Action where
  block : Nat
  occurrence : Label := .pub
  /-- Payload visibility does not determine whether an occurrence exists or is Public. -/
  payload : List Label := []
  deriving Repr

structure Call where
  block : Nat
  target : Nat
  /-- Each possible dynamic target carries the selector's influence. Target-set completeness is
      an input obligation of this reference problem, not proved from closure captures here. -/
  selection : Label := .pub
  deriving Repr

structure Function where
  graph : Graph
  actions : List Action := []
  calls : List Call := []
  deriving Repr, Inhabited

abbrev Program := Array Function

def wellFormed (p : Program) : Bool :=
  p.all (fun f => f.graph.wellFormed &&
    f.actions.all (fun a => a.block < f.graph.size && a.occurrence != .secretCT) &&
    f.calls.all (fun c => c.block < f.graph.size && c.target < p.size))

/-- A call propagates invocation influence, not a replacement return or payload label. -/
def invocationStep (p : Program) (labels : Array Label) : Array Label :=
  (List.range p.size).foldl (fun next caller =>
    let f := p[caller]!
    f.calls.foldl (fun next call =>
      let influence := ((labels.getD caller .pub).lub
        (localInfluence f.graph call.block)).lub call.selection
      next.set! call.target ((next.getD call.target .pub).lub influence)) next)
    labels

def invocationIterate (p : Program) : Nat → Array Label → Array Label
  | 0, labels => labels
  | fuel + 1, labels => invocationIterate p fuel (invocationStep p labels)

def invocationLabels (p : Program) : Array Label :=
  invocationIterate p (3 * p.size) (Array.replicate p.size .pub)

/-- This explicit closure check is load-bearing until the bounded iteration theorem is proved.
    Fuel exhaustion is not treated as evidence of a fixed point. -/
def invocationClosed (p : Program) (labels : Array Label) : Bool :=
  labels.size == p.size && invocationStep p labels == labels

def actionsSafe (p : Program) (labels : Array Label) : Bool :=
  (List.range p.size).all (fun function =>
    let f := p[function]!
    f.actions.all (fun action =>
      ((labels.getD function .pub).lub (localInfluence f.graph action.block)).flowsTo action.occurrence))

def classify (p : Program) : Bool :=
  let labels := invocationLabels p
  wellFormed p && p.all (fun f => localClosed f.graph) &&
    invocationClosed p labels && actionsSafe p labels

theorem accepted_invocations_are_closed (p : Program) (h : classify p = true) :
    invocationClosed p (invocationLabels p) = true := by
  exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).2

theorem accepted_actions_are_safe (p : Program) (h : classify p = true) :
    actionsSafe p (invocationLabels p) = true := by
  exact (Bool.and_eq_true_iff.mp h).2

private def action (block : Nat) (occurrence : Label := .pub)
    (payload : List Label := []) : Action := ⟨block, occurrence, payload⟩

private def linear : Graph := ⟨#[[1], []], [1], #[.pub, .pub]⟩

/-- The header runs once or twice; the exit is a genuine continuation. -/
def secretLoop : Graph := ⟨#[[1, 2], [0], []], [2], #[.secret, .pub, .pub]⟩

theorem secret_loop_header_is_controlled : controls secretLoop 0 0 = true := by decide +kernel
theorem secret_loop_exit_is_not_controlled : controls secretLoop 0 2 = false := by decide +kernel
theorem public_loop_header_action_rejected :
    classify #[⟨secretLoop, [action 0], []⟩] = false := by decide +kernel
theorem public_loop_continuation_accepted :
    classify #[⟨secretLoop, [action 2], []⟩] = true := by decide +kernel

def setupThenSecretLoop : Graph :=
  ⟨#[[1], [2, 3], [1], []], [3], #[.pub, .secret, .pub, .pub]⟩

theorem one_time_public_setup_accepted :
    classify #[⟨setupThenSecretLoop, [action 0, action 3], []⟩] = true := by decide +kernel

/-- A private branch inside a Public loop rejoins before the action at block four. SCC-wide
    selector taint would incorrectly reject this graph. -/
def balancedBranch : Graph :=
  ⟨#[[1, 5], [2, 3], [4], [4], [0], []], [5],
    #[.pub, .secret, .pub, .pub, .pub, .pub]⟩

theorem balanced_private_branch_public_action_accepted :
    classify #[⟨balancedBranch, [action 0, action 4, action 5], []⟩] = true := by decide +kernel
theorem private_arm_public_action_rejected :
    classify #[⟨balancedBranch, [action 2], []⟩] = false := by decide +kernel

def nestedPrivateBranch : Graph :=
  ⟨#[[1, 5], [2, 3], [4], [4], [5], []], [5],
    #[.secret, .pub, .pub, .pub, .pub, .pub]⟩

theorem nested_public_selector_remains_private :
    classify #[⟨nestedPrivateBranch, [action 2], []⟩] = false := by decide +kernel
theorem nested_private_branch_public_continuation_accepted :
    classify #[⟨nestedPrivateBranch, [action 5], []⟩] = true := by decide +kernel

def secretBreak : Graph :=
  ⟨#[[1, 3], [2, 3], [0], []], [3], #[.pub, .secret, .pub, .pub]⟩

theorem secret_break_controls_repeated_header : controls secretBreak 1 0 = true := by decide +kernel
theorem secret_break_public_header_rejected :
    classify #[⟨secretBreak, [action 0], []⟩] = false := by decide +kernel
theorem secret_break_public_continuation_accepted :
    classify #[⟨secretBreak, [action 3], []⟩] = true := by decide +kernel

def secretContinue : Graph :=
  ⟨#[[1, 4], [0, 2], [3], [0], []], [4], #[.pub, .secret, .pub, .pub, .pub]⟩

theorem secret_continue_skipped_action_rejected :
    classify #[⟨secretContinue, [action 2], []⟩] = false := by decide +kernel
theorem secret_continue_does_not_blanket_taint_header :
    classify #[⟨secretContinue, [action 0, action 4], []⟩] = true := by decide +kernel

/-- The acyclic backwards edge is not a loop backedge and conveys no restoration privilege. -/
def acyclicBackwardEscape : Graph :=
  ⟨#[[2, 3], [], [1], [4], []], [1, 4], #[.secret, .pub, .pub, .pub, .pub]⟩

theorem acyclic_backward_escape_public_actions_rejected :
    classify #[⟨acyclicBackwardEscape, [action 1, action 4], []⟩] = false := by decide +kernel

theorem pure_helper_without_actions_accepted :
    classify #[⟨secretLoop, [], [⟨0, 1, .pub⟩]⟩, ⟨linear, [], []⟩] = true := by decide +kernel
theorem effectful_header_helper_rejected :
    classify #[⟨secretLoop, [], [⟨0, 1, .pub⟩]⟩, ⟨linear, [action 0], []⟩] = false := by decide +kernel
theorem transitive_header_helper_rejected :
    classify #[⟨secretLoop, [], [⟨0, 1, .pub⟩]⟩, ⟨linear, [], [⟨0, 2, .pub⟩]⟩,
      ⟨linear, [action 0], []⟩] = false := by decide +kernel
theorem recursive_header_helper_rejected :
    classify #[⟨secretLoop, [], [⟨0, 1, .pub⟩]⟩, ⟨linear, [action 0], [⟨0, 1, .pub⟩]⟩] = false := by
  decide +kernel
theorem private_header_helper_accepted :
    classify #[⟨secretLoop, [], [⟨0, 1, .pub⟩]⟩, ⟨linear, [action 0 .secret], []⟩] = true := by
  decide +kernel

theorem private_dynamic_target_public_effect_rejected :
    classify #[⟨linear, [], [⟨0, 1, .secret⟩, ⟨0, 2, .secret⟩]⟩,
      ⟨linear, [action 0], []⟩, ⟨linear, [], []⟩] = false := by decide +kernel

theorem private_dynamic_target_pure_helpers_accepted :
    classify #[⟨linear, [], [⟨0, 1, .secret⟩, ⟨0, 2, .secret⟩]⟩,
      ⟨linear, [], []⟩, ⟨linear, [], []⟩] = true := by decide +kernel

theorem public_occurrence_secret_payload_accepted :
    classify #[⟨linear, [action 0 .pub [.secret]], []⟩] = true := by decide +kernel
theorem secret_occurrence_empty_payload_rejected :
    classify #[⟨secretLoop, [action 0 .pub []], []⟩] = false := by decide +kernel
theorem secret_occurrence_secret_payload_rejected :
    classify #[⟨secretLoop, [action 0 .pub [.secret]], []⟩] = false := by decide +kernel

theorem malformed_target_rejected :
    classify #[⟨⟨#[[8]], [], #[.pub]⟩, [], []⟩] = false := by decide +kernel
theorem malformed_call_rejected :
    classify #[⟨linear, [], [⟨0, 7, .pub⟩]⟩] = false := by decide +kernel
theorem inconsistent_terminal_rejected :
    classify #[⟨⟨#[[0]], [0], #[.pub]⟩, [], []⟩] = false := by decide +kernel
theorem nonreturning_cycle_cannot_supply_postdominance :
    postdominates ⟨#[[0]], [], #[.secret]⟩ 0 0 = false := by decide +kernel

/-- Test-only mutation: dropping invocation influence silently re-admits a Public effect in a
    pure-looking header call. The real checker must inspect effects of invocation transitively. -/
def ignoreInvocationMutant (p : Program) : Bool :=
  wellFormed p && actionsSafe p (Array.replicate p.size .pub)

theorem missing_invocation_mutant_readmits_header_effect :
    ignoreInvocationMutant #[⟨secretLoop, [], [⟨0, 1, .pub⟩]⟩,
      ⟨linear, [action 0], []⟩] = true := by decide +kernel

/-- Test-only mutation: filtering actions by Public payload incorrectly removes zero-payload and
    Secret-payload occurrences. This is independent of ordinary payload-flow checks. -/
def payloadFilteredMutant (p : Program) : Bool :=
  classify (p.map fun f => { f with
    actions := f.actions.filter fun a => a.payload.any (· == .pub) })

theorem empty_payload_mutant_readmits_private_occurrence :
    payloadFilteredMutant #[⟨secretLoop, [action 0], []⟩] = true := by decide +kernel
theorem secret_payload_mutant_readmits_private_occurrence :
    payloadFilteredMutant #[⟨secretLoop, [action 0 .pub [.secret]], []⟩] = true := by decide +kernel

/-- Test-only mutation: treating every selector in an SCC as controlling the entire loop would
    label the shared header Secret. The positive balanced-branch witness excludes that shortcut. -/
theorem blanket_scc_mutant_rejects_balanced_branch :
    actionsSafe #[⟨balancedBranch, [action 0, action 4], []⟩] #[.secret] = false := by
  decide +kernel

/-- Same cycle and exit with the header moved to the last numeric position. -/
def permutedSecretLoop : Graph := ⟨#[[], [2], [1, 0]], [0], #[.pub, .pub, .secret]⟩

theorem permuted_secret_loop_header_rejected :
    classify #[⟨permutedSecretLoop, [action 2], []⟩] = false := by decide +kernel
theorem permuted_secret_loop_exit_accepted :
    classify #[⟨permutedSecretLoop, [action 0], []⟩] = true := by decide +kernel

theorem duplicate_edges_do_not_exhaust_search_early :
    let g : Graph := ⟨#[[1, 1, 1, 1], [2], []], [2], #[.pub, .pub, .pub]⟩
    canSucceed g none 0 = true := by decide +kernel

end LambdaSigil.Combined.OccurrenceReference
