module

public import Mathlib.RingTheory.Finiteness.Defs
public import ReasLib.Topology.Algebra.Module.Adic
public import ReasLib.Topology.Algebra.LinearTopology.Completion

/-!
# Completion of modules with an open adic submodule

Completion preserves the existence of an open adic submodule for a finitely
generated ideal and identifies the quotients by positive powers of the ideal.
-/

@[expose] public section

universe u v

open scoped Topology

namespace IsLinearTopology.Completion

variable {R : Type u} {M : Type v}
variable [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable [AddCommGroup M] [Module R M] [TopologicalSpace M]
variable [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]

/-- For a finitely generated ideal `I` and an open `I`-adic submodule `N` of a
topological module `M`, the range of the completed inclusion is an open `I`-adic
submodule of the completion of `M`. -/
theorem isOpen_isAdic_range_map_subtype
    (I : Ideal R) (hI : I.FG) (N : Submodule R M)
    (hN : IsOpen (N : Set M)) (hAdic : Module.IsAdic I N) :
    IsOpen (LinearMap.range (map_subtype N) : Set (Completion R M)) ∧
      Module.IsAdic I (LinearMap.range (map_subtype N)) :=
  sorry

/-- If a topological module has an open `I`-adic submodule for a finitely generated
ideal `I`, then for every positive `n` its canonical map to the completion modulo
`I ^ n • ⊤` is surjective and has kernel `I ^ n • ⊤`. -/
theorem pow_smul_mkQ_comp_of
    (I : Ideal R) (hI : I.FG) (N : Submodule R M)
    (hN : IsOpen (N : Set M)) (hAdic : Module.IsAdic I N)
    {n : ℕ} (hn : 0 < n) :
    LinearMap.ker ((I ^ n • ⊤ : Submodule R (Completion R M)).mkQ ∘ₗ of) =
      I ^ n • ⊤ ∧
    Function.Surjective ((I ^ n • ⊤ : Submodule R (Completion R M)).mkQ ∘ₗ of) :=
  sorry

/-- The inverse-limit completion of an open `I`-adic submodule is `I`-adic. -/
theorem isAdic
    (I : Ideal R) (hI : I.FG) (N : Submodule R M)
    (hN : IsOpen (N : Set M)) (hAdic : Module.IsAdic I N) :
    Module.IsAdic I (Completion R N) :=
  sorry

end IsLinearTopology.Completion
