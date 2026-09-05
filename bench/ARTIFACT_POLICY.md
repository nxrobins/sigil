# Benchmark artifact policy

Benchmark source and benchmark output have different lifetimes. This policy
keeps enough evidence to reproduce published claims without turning the Git
history into a run cache.

## Source and reproducibility inputs

Hand-authored benchmark task YAML, reference SIGIL sources, fixture inputs,
and exporter scripts under `bench/` belong in this repository. Bulk generated
pools and other model-development artifacts do not; they would turn
application-repository history into a run cache.

## Local run output

`bench/runs/` and `var/pipeline/` are ignored operator state. The regular
`sigil-bench run` command keeps the newest 10 eligible run directories by
default. It never removes a directory with a `lock` sentinel or one whose
`run_id.txt` is less than six hours old. `--keep-last-runs N` changes the local
limit; negative limits are rejected.

Do not force-add raw runs. A published run may retain only its compact audit
surface in Git:

- preregistration, summary, report, and run identifier;
- `transcripts.archive.json`, naming a versioned release asset and its SHA-256;
- `transcripts.sha256`, listing every file contained in that archive.

Raw transcripts belong in the release asset, not under `bench/runs/`. The
archive digest is the authority if the hosting URL or transport is untrusted.
To publish evidence:

1. Produce a deterministic archive from the raw transcript tree.
2. Publish it under a versioned release tag.
3. Retain the compact files above and cite the run from a current document
   under `docs/`.
4. Add the run identifier to `bench/published-runs.txt`.

CI rejects tracked training-workspace payloads, raw transcripts, unlisted run
directories, and incomplete compact bundles. Uncited experiments, intermediate
checkpoints, logs, caches, and superseded comparisons stay local and can be
regenerated.

To audit an archived run, download the asset, verify the archive digest from
`transcripts.archive.json`, extract it at the repository root, and check every
entry in `transcripts.sha256`.

## Archive locations

A run's `transcripts.archive.json` names its externally retained transcript archive with a
`release:<tag>/<asset>` URL: the asset of that name attached to the GitHub release `<tag>` of
this repository (the `origin` remote). The `archive_sha256` field binds the bytes whatever the
host, so a reader who fetches the asset from any mirror can verify it. Publishing a run means
attaching its archive to that release wherever the repository lives.
