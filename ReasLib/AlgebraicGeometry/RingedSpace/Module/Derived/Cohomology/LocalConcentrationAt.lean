module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.LocalConcentration

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- A derived module is locally concentrated in one degree at a point when some open
neighborhood of that point has one common concentration degree for all derived stalks. -/
def IsLocallyConcentratedAt (E : ModuleDerived X) (x : X) : Prop :=
  ∃ U : Opens X, x ∈ U ∧ ∃ n : ℤ, ∀ y : X, y ∈ U →
    DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk y)) n (Stalk.obj E y)

/-- The neighborhoodwise characterization of local concentration at a point. -/
theorem isLocallyConcentratedAt_iff (E : ModuleDerived X) (x : X) :
    IsLocallyConcentratedAt E x ↔
      ∃ U : Opens X, x ∈ U ∧ ∃ n : ℤ, ∀ y : X, y ∈ U →
        DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk y)) n
          (Stalk.obj E y) := sorry

namespace IsLocallyConcentratedAt

/-- Local concentration at a point is invariant under isomorphism of derived modules. -/
theorem of_isIsomorphic {E E' : ModuleDerived X} {x : X}
    (hE : IsLocallyConcentratedAt E x) (h : IsIsomorphic E E') :
    IsLocallyConcentratedAt E' x := sorry

end IsLocallyConcentratedAt
end AlgebraicGeometry.RingedSpace.ModuleDerived
