module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RegularVanishing

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- A cohomology gap of the dimension of a regular Noetherian scheme splits a bounded coherent
complex into its lower and upper truncations. -/
theorem truncation_split_of_cohomology_vanishing
    {X : Scheme.{u}} [IsNoetherian X] [Scheme.Regular X]
    (d : ℕ) (h_dimension : topologicalKrullDim X = d)
    (K : Dᵇ[SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf])
    (a : ℤ)
    (hvanish : ∀ i : ℤ, a < i → i < a + (d : ℤ) →
      IsZero ((DerivedCategory.Bounded.homologyFunctor X.Modules i).obj K.obj)) :
    ∃ e : K.obj.obj ≅
        (DerivedCategory.TStructure.t.truncLE a).obj K.obj.obj ⊞
          (DerivedCategory.TStructure.t.truncGE (a + (d : ℤ))).obj K.obj.obj,
      ((DerivedCategory.TStructure.t.truncLEι a).app K.obj.obj) ≫ e.hom = biprod.inl ∧
        e.hom ≫ biprod.snd =
          (DerivedCategory.TStructure.t.truncGEπ (a + (d : ℤ))).app K.obj.obj := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
