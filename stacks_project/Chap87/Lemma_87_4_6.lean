/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Algebra.LinearTopology.AdicCompletion
import StacksCheckRecall

/-!
# Lemma 87.4.6

If a linearly topologized module has an open `I`-adic submodule for a finitely
generated ideal `I`, then its inverse-limit completion does as well, and the
canonical maps `M → Completion R M ⧸ I ^ n • ⊤` identify
`Completion R M ⧸ I ^ n • ⊤` with `M ⧸ I ^ n • ⊤` for `n ≥ 1`.
-/

@[expose] public section

universe u v

open scoped Topology

namespace IsLinearTopology.Completion

/- Lemma 87.4.6 (1): if `R` is a topological ring, `M` is a topological `R`-module,
and `I` is a finitely generated ideal such that `N` is an open `I`-adic submodule of
`M`, then `LinearMap.range (map_subtype N)` is an open `I`-adic submodule of
`Completion R M`. -/
@[stacks 0F1S]
#check (IsLinearTopology.Completion.isOpen_isAdic_range_map_subtype :
  ∀ {R : Type u} {M : Type v}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (I : Ideal R) (hI : I.FG) (N : Submodule R M)
    (hN : IsOpen (N : Set M)) (hAdic : Module.IsAdic I N),
    IsOpen (LinearMap.range (map_subtype N) : Set (Completion R M)) ∧
      Module.IsAdic I (LinearMap.range (map_subtype N)))

/- Lemma 87.4.6 (2): if `R` is a topological ring, `M` is a topological `R`-module,
and `I` is a finitely generated ideal such that `N` is an open `I`-adic submodule of
`M`, then for every `n ≥ 1` the canonical map
`(I ^ n • ⊤).mkQ ∘ₗ of : M →ₗ[R] Completion R M ⧸ I ^ n • ⊤` has kernel
`I ^ n • ⊤` and is surjective. -/
@[stacks 0F1S]
#check (IsLinearTopology.Completion.pow_smul_mkQ_comp_of :
  ∀ {R : Type u} {M : Type v}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (I : Ideal R) (hI : I.FG) (N : Submodule R M)
    (hN : IsOpen (N : Set M)) (hAdic : Module.IsAdic I N)
    {n : ℕ} (hn : 0 < n),
    LinearMap.ker ((I ^ n • ⊤ : Submodule R (Completion R M)).mkQ ∘ₗ of) =
      I ^ n • ⊤ ∧
    Function.Surjective ((I ^ n • ⊤ : Submodule R (Completion R M)).mkQ ∘ₗ of))

/- The inverse-limit completion of an open `I`-adic submodule is `I`-adic. -/
#check (IsLinearTopology.Completion.isAdic :
  ∀ {R : Type u} {M : Type v}
    [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (I : Ideal R) (hI : I.FG) (N : Submodule R M)
    (hN : IsOpen (N : Set M)) (hAdic : Module.IsAdic I N),
    Module.IsAdic I (Completion R N))

end IsLinearTopology.Completion
