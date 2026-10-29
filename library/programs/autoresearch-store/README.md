# Autoresearch checkpoint storage consumer

This experimental, unreviewed, unadmitted consumer connects the existing
sigil/storage and sigil/kv packages to the autoresearch checkpoint workflow.
Numerical search and checkpoint validation remain in the separate inner-ring
consumer. No cross-ring source call or implicit label downgrade is introduced.

From the repository root, explicitly lock the graph and build the host:

```sh
sigil package-lock --root library/programs/autoresearch-store --dependency sigil/storage=library/packages/storage --dependency sigil/kv=library/packages/kv
cargo build -p sigil --features solver --example autoresearch-storage
```

The host is a local research example, not a change to the general SIGIL CLI.
It compiles the locked graph freshly, requires the solver witness, checks the
outer Internal-result ABI, permits only the storage effect profile, and runs
with explicit --kv-read and --kv-write roots. Missing grants refuse. It also
requires --allow-public-checkpoint-import; use it only for checkpoints you
declare Public. No input chooses a command, network endpoint or executable.

This public source revision is experimental, unreviewed and not admitted.
The previous package revision and development records remain unchanged.
