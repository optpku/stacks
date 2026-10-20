module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.TorDimension.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Localization
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Local relative Tor dimension on algebraic spaces

Finite Tor dimension over inverse-image coefficients is tested after exact restriction
to slices of the small étale site, with bounds allowed to vary over a covering.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Module sheaves over `f⁻¹𝒪_Y` on the slice of `X_étale` over `U`, with values in
the original coefficient universe. -/
abbrev RelativeOn (f : X ⟶ Y) (U : smallEtaleSite X) :=
  SheafOfModules.{u}
    ((SheafOfModules.RingedSite.ringSheaf (smallEtaleTopology X)
      (commInverseImageStructureSheaf f)).over U)

/-- Inverse-image coefficient modules on an étale slice have the standard derived category. -/
instance relativeOnHasDerivedCategory (f : X ⟶ Y) (U : smallEtaleSite X) :
    HasDerivedCategory (RelativeOn f U) :=
  HasDerivedCategory.standard (RelativeOn f U)

/-- The canonical tensor product of unbounded complexes of inverse-image coefficient
modules on an étale slice admits totalization. -/
instance relativeOnHasMapBifunctor (f : X ⟶ Y) (U : smallEtaleSite X)
    (K L : CochainComplex (RelativeOn f U) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor (RelativeOn f U)) (up ℤ) := sorry

/-- Unbounded fixed-right derived tensor products exist over inverse-image coefficients
on every étale slice. -/
instance relativeOnHasDerivedTensorRight (f : X ⟶ Y) (U : smallEtaleSite X) :
    DerivedCategory.DerivedTensor.Right.Has (C := RelativeOn f U) := sorry

end Modules

namespace ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Exact derived restriction to inverse-image coefficients on the étale slice over `U`. -/
def restrictRelativeTo (f : X ⟶ Y) (U : smallEtaleSite X) :
    ModuleDerived X ⥤ DerivedCategory (Modules.RelativeOn f U) :=
  restrictToRelativeCoefficients f ⋙
    (SheafOfModules.Localization.restriction
      (SheafOfModules.RingedSite.ringSheaf.{u + 1, u, u} (smallEtaleTopology X)
        (commInverseImageStructureSheaf f)) U :
      Modules.Relative f ⥤ Modules.RelativeOn f U).mapDerivedCategory

/-- A derived module locally has finite Tor dimension over `f⁻¹𝒪_Y` if every object
of the small étale site has a covering on whose domains its restriction has finite
Tor dimension over the restricted inverse-image coefficient sheaf. -/
def locallyFiniteTorDimensionOver (f : X ⟶ Y) : ObjectProperty (ModuleDerived X) :=
  fun E ↦ ∀ U : smallEtaleSite X, ∃ T : (smallEtaleTopology X).Cover U, ∀ I : T.Arrow,
    DerivedCategory.DerivedTensor.HasFiniteTorDimension ((restrictRelativeTo f I.Y).obj E)

/-- Local finite Tor dimension over inverse-image coefficients is equivalent to
finite Tor dimension after restriction to every domain of a covering of each site object. -/
theorem locallyFiniteTorDimensionOver_iff (f : X ⟶ Y) (E : ModuleDerived X) :
    locallyFiniteTorDimensionOver f E ↔
      ∀ U : smallEtaleSite X, ∃ T : (smallEtaleTopology X).Cover U, ∀ I : T.Arrow,
        DerivedCategory.DerivedTensor.HasFiniteTorDimension
          ((restrictRelativeTo f I.Y).obj E) := sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
