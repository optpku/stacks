# Contributing proofs

**Everyone is welcome to submit a GitHub Pull Request containing a Lean proof.**
You can complete a theorem, prove a shared supporting lemma, improve a definition,
or report a mismatch with the mathematical source. Contributions of any size are
welcome; a single completed lemma is useful.

## Find a contribution

Browse [`stacks_project/`](stacks_project/) by chapter, or choose a file from
[`docs/proof-debt.tsv`](docs/proof-debt.tsv). The list records explicit `sorry`
placeholders in the imported snapshot. It is a starting point, not a statement
that a file is mathematically correct or that all of its dependencies are proved.

Read the corresponding [Stacks Project](https://stacks.math.columbia.edu/) result.
Where present, an attribute such as `@[stacks 0DPK]` identifies the source at
<https://stacks.math.columbia.edu/tag/0DPK>. Prefer stable tags over chapter numbers
when identifying the source in a PR. If a file has no tag, give its source section
and explain the correspondence.

Open an issue or comment on an existing one to coordinate substantial work. You
can submit a small proof directly as a PR; no task-claim bot or special command is
required.

## Submit a proof

1. Fork the GitHub repository and create a branch for your contribution.
2. Replace the intended `sorry` with a Lean proof. Put reusable mathematical
   infrastructure in `ReasLib/` and source-specific results in `stacks_project/`.
3. Preserve theorem statements and source tags where possible. Explain necessary
   changes to definitions, hypotheses, namespaces, or imports in the PR.
4. Validate the changed modules with the pinned Lean toolchain and dependencies.
5. Open a Pull Request against the repository's default branch. Include the file,
   declaration name, source tag or section, proof summary, and validation result.

Do not discharge a proof by introducing a new axiom, leaving `sorry` in new
helpers, assuming the theorem itself, or weakening the intended mathematical
statement. Existing imported dependencies may still have proof debt; disclose
that debt when it affects the result. A proof PR does not need to solve every
unrelated placeholder in the repository.

## Contributor setup and validation

Install Lean using the [Lean community installation guide](https://leanprover-community.github.io/get_started.html).
The `lean-toolchain` file selects the version. Keep both the toolchain and
`lake-manifest.json` unchanged unless your PR intentionally updates dependencies.

For contributors preparing their own environment:

```bash
lake exe cache get
lake env lean stacks_project/Chap108/Lemma_108_9_5.lean
```

Replace the example path with the module you changed. If project dependencies
need building, build the relevant target in your own validation environment
before checking the file. Mention any validation that could not be completed.
The publication snapshot itself was imported without local compilation; there is
no claim that the full project has passed a clean build.

Keep PRs focused. Explain whether helper lemmas can be upstreamed to mathlib,
avoid unrelated reformatting, and preserve existing source attribution and
third-party notices. Maintainers review the mathematical correspondence as well
as the Lean proof.

## Updating the proof inventory

The following command only reads source text and regenerates the inventory;
it does not run Lean or Lake:

```bash
python3 scripts/proof_inventory.py
```

## 中文说明

欢迎所有人通过 **GitHub Pull Request 提交 Lean 证明**，包括单个引理的证明、
公共辅助引理以及声明修正。请注明对应的 Stacks tag、文件和声明名称，说明证明思路
及验证结果。可以从 `docs/proof-debt.tsv` 中选择包含 `sorry` 的文件；不要用新增公理
或削弱原命题来代替证明。

## Author credits and statistics

Lean files carry separate credits for statement formalization and proof
formalization. Both currently use `ReasBook team` as a temporary team credit.
Describe your role in your Pull Request and update the relevant credit when
agreed with the maintainers. Preserve existing author notices and source tags.
Completing a shared-library result can benefit multiple chapter statements;
identify the reused module as well as the chapter source where applicable.

To regenerate source inventories without invoking Lean or Lake, run:

```sh
python3 scripts/formalization_statistics.py
python3 scripts/proof_inventory.py
```

Update the statistics tables in both README language versions from the generated
reports when refreshing a publication. Keep service-reported stage counts
separate from static source counts; remote coverage and chapter-source coverage
are different. Neither absence of a placeholder nor an integration success is
an independent proof certificate.

When importing a new remote snapshot, `scripts/add_author_headers.py` adds
placeholder author comments and records preservation of the original source
bodies. Keep personalized contributor credits when refreshing existing files.
