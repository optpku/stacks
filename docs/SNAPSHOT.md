# Publication snapshot

The source snapshot was exported from the remote `stacks` repository on
October 7, 2026 as a Lean project ZIP. Archive CRC checks passed before extraction.

## Import policy

All Lean source files in `ReasLib/`, `stacks_project/`, and `M2FQualityAudits/`,
the root modules `ReasLib.lean` and `stacks.lean`, and the original
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` were preserved.
Source bytes and dependency pins are unchanged.

Runtime state, integration execution records, agent memory, local probe/log
output at the archive root, non-source orchestration documents, and compiled
artifacts were omitted. Public documentation, contribution templates, a source
inventory script, the chosen Apache-2.0 license, and publication ignore rules
were added separately.

The remote package layout is retained. The archive did not contain a top-level
`stacks_project.lean` or `M2FQualityAudits.lean`; no new umbrella module or altered
build configuration was synthesized during import.

## Reproducibility

[`import-manifest.json`](import-manifest.json) records the archive SHA-256,
download time, extraction policy, and SHA-256 of every imported file.
The imported `.gitignore` was replaced with publication-specific rules;
its original hash remains in the manifest as provenance.

The archive is a working-tree snapshot of an active remote repository, not a
tagged upstream Git release. It has no upstream Git history and does not
guarantee that every file was captured at one transactional instant.
No private service URL or credential is required to use the published source.

## Validation performed

- ZIP member paths and link types were checked before extraction.
- Archive CRC checks passed.
- Imported Lean sources and dependency files were preserved without editing.
- A textual scan of Lean sources found no user API key patterns, private-key
  blocks, backend URLs, or private workspace paths.
- Source inventories were generated without invoking Lean or Lake.

**No local compilation, dependency download, Lake update, or proof validation was
performed.** Explicit `sorry` counts are lexical measurements, not proof
certificates or live backend pipeline status.
