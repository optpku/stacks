# Publication snapshot

The source snapshot was exported from the remote `stacks` repository as a Lean
project ZIP. Archive CRC checks passed before extraction. Each refresh replaces
the previously imported source tree with the new remote snapshot, including
removing source files that are no longer present remotely.

## Import policy

All Lean source files in `ReasLib/`, `stacks_project/`, and `M2FQualityAudits/`,
the root modules `ReasLib.lean` and `stacks.lean`, and the original
`lean-toolchain`, `lakefile.toml`, and `lake-manifest.json` were preserved.
Dependency pins match the downloaded remote snapshot. Published Lean sources
have license and license and author-credit block comments prepended, separately crediting statement and
proof formalization to `ReasBook team`. The original source bytes following
these headers are unchanged, including any existing author notices.

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
download time, extraction policy, and SHA-256 of every original imported file.
Those original hashes describe the remote import before publication headers.
[`author-header-manifest.json`](author-header-manifest.json) records the original
and published hashes and header size for every modified Lean source. Removing
only the added header recovers the exact original imported bytes.
Publication-specific ignore rules, documentation, contribution templates, and
the chosen license are maintained separately from the imported remote code.

The archive is a working-tree snapshot of an active remote repository, not a
tagged upstream Git release. It has no upstream Git history and does not
guarantee that every file was captured at one transactional instant.
No private service URL or credential is required to use the published source.

## Validation performed

- ZIP member paths and link types were checked before extraction.
- Archive CRC checks passed.
- Removing each added author-credit comment reproduces its original imported
  Lean source byte for byte; dependency files remain unchanged.
- All published Lean sources have separate statement and proof author credits;
  all publication Python scripts have author credits.
- A textual scan of Lean sources found no user API key patterns, private-key
  blocks, backend URLs, or private workspace paths.
- Source inventories were generated without invoking Lean or Lake.

**No local compilation, dependency download, Lake update, or proof validation was
performed.** Static `sorry`/`admit` and declaration counts are lexical measurements, not proof
certificates. The separate backend progress record contains service-reported
counts from its returned cache snapshot; its scope is registered service items,
not all imported chapter and shared-library source.
