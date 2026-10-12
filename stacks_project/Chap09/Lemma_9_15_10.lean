/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.Normal.Defs
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

/- Domain-style sampling for Lemma 9.15.10:
- primary domain: `K`-embeddings of a normal algebraic extension `L/K` into another extension `E/K`,
  and their transitive free action by `Aut(L/K)`;
- sampled owner declarations:
  `Normal`,
  `AlgHom.restrictNormal'`,
  `Normal.algHomEquivAut`;
- best owner abstraction: the canonical owner is the mathlib equivalence `Normal.algHomEquivAut`,
  which for a tower `E/L/K` with `L/K` normal identifies the `K`-embeddings `L →ₐ[K] E` with the
  automorphism group `Aut(L/K) = L ≃ₐ[K] L`;
- primitive data: none locally beyond the ambient tower `E/L/K` and the normality of `L/K`;
- derived API: the inverse of `Normal.algHomEquivAut` sends `σ ∈ Aut(L/K)` to `τ ∘ σ`, where `τ` is
  the fixed base embedding `L ↪ E`; this is exactly the textbook description of the other
  embeddings.

Source/core/bridge triage:
- `source-facing`: given a fixed `K`-embedding `τ : L → E`, every `K`-embedding `L → E` is of the
  form `τ ∘ σ` for a unique `σ ∈ Aut(L/K)` (and there is no embedding at all otherwise);
- `core/canonical`: `Normal.algHomEquivAut`;
- `bridge/view`: reading off the `invFun` component `σ ↦ τ ∘ σ` and its bijectivity.

This item adds no new mathematics beyond the canonical owner, which mathlib itself tags with the
Stacks tag `0BR4`, so the file remains a pure check surface rather than introducing a redundant
local wrapper. -/

/- Lemma 9.15.10: let `L/K` be an algebraic normal extension of fields and let `E/K` be any
extension. Then either there is no `K`-embedding `L → E`, or, fixing one such embedding `τ`, every
`K`-embedding `L → E` is of the form `τ ∘ σ` for a unique `σ ∈ Aut(L/K)`. For a tower `E/L/K` with
`L/K` normal this is the canonical mathlib equivalence `Normal.algHomEquivAut : (L →ₐ[K] E) ≃
(L ≃ₐ[K] L)`, whose inverse sends `σ` to `τ ∘ σ` for the tower inclusion `τ : L ↪ E`. -/
@[stacks 0BR4]
#check Normal.algHomEquivAut
