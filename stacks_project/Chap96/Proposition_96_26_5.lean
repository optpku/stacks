module

public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap96.Proposition_96_26_5_Comparison
public import stacks_project.Chap96.Proposition_96_26_5_Groupoids

/-!
# Quasi-coherent derived objects on Spf of an adic Noetherian algebra
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Proposition 96.26.5: let `S` be a scheme and let `A` be an adic Noetherian topological
`S`-algebra with ideal of definition `I`. Write `X = Spf(A)` and let `𝒳` be the category
fibred in sets associated to the fppf functor `X`. Then `QC(𝒳)` is canonically equivalent
to the category `D_comp(A, I)` of objects of `D(A)` which are derived complete with
respect to `I`. -/
@[stacks 0H0L, instance]
instance toDerivedComplete_isEquivalence
    {A : Type u} [CommRing A] [TopologicalSpace A] [IsNoetherianRing A]
    [TopologicalRing.IsAdicRing A] (structureHom : Spec (.of A) ⟶ S)
    [HasWeakSheafify (Scheme.fppfTopology.over S) (Type u)]
    (I : Ideal A) (hI : TopologicalRing.Ideal.IsIdealOfDefinition I) :
    (toDerivedComplete structureHom I hI).IsEquivalence :=
  sorry

end AlgebraicGeometry.GroupoidsOver
