# The DAO (2016): Solidity reentrancy via send-before-state-update

**Affected:** "The DAO" smart contract on Ethereum mainnet, June 2016
**CVE record:** No formal CVE; documented at https://en.wikipedia.org/wiki/The_DAO
**Severity:** ~$60M USD drained at the time (~$11B USD at peak ETH price)
**Scope of claim:** CLASS

## What was the bug

The DAO ("Decentralized Autonomous Organization") was an Ethereum smart contract that pooled investor funds and let participants vote on investment proposals. Investors could withdraw their share at any time via a `splitDAO` function.

`splitDAO`'s logic was: (a) calculate the user's share, (b) send them the corresponding ether, (c) deduct the share from the user's balance. The bug was the ORDER: the ether send happened BEFORE the balance update.

In Solidity, sending ether to an address can trigger that address's `fallback` function. If the recipient is a contract under attacker control, that fallback can RE-ENTER `splitDAO` while the original call is still on the stack. The reentrant call sees the still-non-zero balance and processes another withdrawal. Repeat until the contract is drained.

## How attackers exploited it

In June 2016 an attacker deployed a malicious "split" contract that, when receiving ether from The DAO, recursively called `splitDAO` again. Each recursive call drained another share. Over the course of several blocks, the attacker drained ~3.6M ETH (~$60M at the time).

The Ethereum community ultimately responded with a contentious hard fork that reversed the attack — splitting Ethereum into ETH (post-fork) and Ethereum Classic (pre-fork). The DAO bug is the defining event in smart-contract security history.

## SIGIL's defense

SIGIL's actor model uses **asynchronous message passing**. A `vault.send(Process(...))` does not synchronously invoke any code on the receiver — it appends a message to the receiver's mailbox. There is no equivalent of Solidity's synchronous external call; reentrancy in the DAO's sense is **architecturally inexpressible**.

The CLOSEST analog in SIGIL terms is the linear-capability use-after-move pattern. A withdrawal capability (`Withdrawal`) is consumed by the first `send(Process(cap))`. Any attempt to invoke withdraw a second time requires a second cap — and that cap doesn't exist unless the vault chooses to mint one.

This is not a faithful port of the DAO bug (the original bug had no notion of linear caps). It IS the closest SIGIL primitive in the same defensive role: "you can't withdraw twice from a one-time authorization." The ownership checker fires O001 at the second `send`.

## Vulnerable shape

See [`03_dao_reentrancy.sigil`](03_dao_reentrancy.sigil).

```sigil
on Tick(vref: ActorRef<Vault>) -> i64 {
    vref.send(Process(withdraw_cap));
    vref.send(Process(withdraw_cap));   // O001 — use-after-move
    return 1;
}
```

## Safe alternative

See [`03_dao_reentrancy_safe.sigil`](03_dao_reentrancy_safe.sigil). Single move, single withdrawal; the cap is consumed exactly once.

## Defense layer

| Original language | Defense gap | SIGIL primitive | Diagnostic |
|---|---|---|---|
| Solidity | Synchronous external calls + post-call state update | Async actor messages + linear capability discipline | O001 |

## Citations

- https://en.wikipedia.org/wiki/The_DAO
- https://www.coindesk.com/learn/2016/06/25/understanding-the-dao-attack/
- https://hackingdistributed.com/2016/06/18/analysis-of-the-dao-exploit/
