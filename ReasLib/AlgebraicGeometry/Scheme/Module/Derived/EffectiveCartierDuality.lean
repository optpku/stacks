module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.ProjectionFormula.ClosedEmbedding
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Normal
public import ReasLib.CategoryTheory.Monoidal.Adjunction.SupportedTensor

/-!
# Derived duality for effective Cartier divisors

This module identifies the derived dual of the structure sheaf of an effective Cartier divisor
with its shifted normal sheaf.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- For an effective Cartier divisor `i : D ⟶ X`, a right adjoint to derived pushforward sends
the degree-zero structure sheaf of `X` to the degree-zero normal sheaf of `i`, shifted by `-1`. -/
theorem rHomStructureSheaf_isomorphic_normalSheaf_shift
    {X D : Scheme.{u}} (i : D ⟶ X) [IsEffectiveCartierDivisor i]
    (rHomOD : RingedSpace.ModuleDerived X.toRingedSpace ⥤
      RingedSpace.ModuleDerived D.toRingedSpace)
    (rHomODAdjunction :
      RingedSpace.moduleDerivedPushforward i.toShHom ⊣ rHomOD) :
    IsIsomorphic
      (rHomOD.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj
          (SheafOfModules.unit X.ringCatSheaf)))
      (((DerivedCategory.singleFunctor D.Modules 0).obj
        (Hom.normalSheaf i))⟦(-1 : ℤ)⟧) := sorry

namespace EffectiveCartierDuality

/-- The normal sheaf of `i : D ⟶ X`, embedded in `D(𝒪_D)` and shifted by `-1`. -/
noncomputable def normalShift {X D : Scheme.{u}} (i : D ⟶ X) :
    RingedSpace.ModuleDerived D.toRingedSpace :=
  ((DerivedCategory.singleFunctor D.Modules 0).obj (Hom.normalSheaf i))⟦(-1 : ℤ)⟧

/-- The named normal-shift object unfolds to the shifted degree-zero normal sheaf. -/
theorem normalShift_def {X D : Scheme.{u}} (i : D ⟶ X) :
    normalShift i =
      ((DerivedCategory.singleFunctor D.Modules 0).obj (Hom.normalSheaf i))⟦(-1 : ℤ)⟧ := sorry

variable {X D : Scheme.{u}} (i : D ⟶ X) [IsEffectiveCartierDivisor i]
variable [KFlat.HomotopyTensorDescends X.toRingedSpace]
variable [KFlat.TensorDescends X.toRingedSpace]
variable [KFlat.IsLocalization X.toRingedSpace]
variable [KFlat.HomotopyTensorDescends D.toRingedSpace]
variable [KFlat.TensorDescends D.toRingedSpace]
variable [KFlat.IsLocalization D.toRingedSpace]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom i.toShHom)]
variable [Functor.HasLeftDerivedFunctor
  (RingedSpace.modulePullbackToDerived i.toShHom)
  (RingedSpace.ModuleQis X.toRingedSpace)]
variable [HasWeakSheafify (Opens.grothendieckTopology D.toRingedSpace) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology D.toRingedSpace).WEqualsLocallyBijective
  AddCommGrpCat.{u}]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived i.toShHom)]

variable (rHomOD : RingedSpace.ModuleDerived X.toRingedSpace ⥤
  RingedSpace.ModuleDerived D.toRingedSpace)
variable (rHomODAdjunction :
  RingedSpace.moduleDerivedPushforward i.toShHom ⊣ rHomOD)
variable (structureSheafUnitIso :
  (DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf) ≅
    𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
variable (normalIdentification :
  rHomOD.obj ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) ≅ normalShift i)

/-- The component at `K` of the effective-Cartier tensor-duality comparison. -/
noncomputable def comparisonApp (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (RingedSpace.modulePullbackDerived i.toShHom).obj K ⊗ normalShift i ⟶
      rHomOD.obj K :=
  (𝟙 _ ⊗ₘ normalIdentification.inv) ≫
    (@CategoryTheory.Adjunction.supportTensor _ _ _ _ _ _ _ _ _
      (RingedSpace.modulePullbackDerivedPushforwardAdjunction i.toShHom)
      rHomODAdjunction _
      (ClosedEmbedding.projectionFormula i.toShHom
        (IsClosedImmersion.isClosedEmbedding i)) K
      ((DerivedCategory.singleFunctor X.Modules 0).obj
        (SheafOfModules.unit X.ringCatSheaf))) ≫
    rHomOD.map
      ((𝟙 K ⊗ₘ structureSheafUnitIso.hom) ≫ (ρ_ K).hom)

/-- The effective-Cartier tensor-duality components commute with morphisms of ambient
derived modules. -/
theorem comparisonApp_naturality {K L : RingedSpace.ModuleDerived X.toRingedSpace}
    (f : K ⟶ L) :
    (RingedSpace.modulePullbackDerived i.toShHom ⋙
        tensorRight (normalShift i)).map f ≫
        comparisonApp i rHomOD rHomODAdjunction structureSheafUnitIso
          normalIdentification L =
      comparisonApp i rHomOD rHomODAdjunction structureSheafUnitIso
          normalIdentification K ≫ rHomOD.map f := sorry

/-- The effective-Cartier tensor-duality comparison, functorial in the ambient derived module. -/
noncomputable def comparison :
    RingedSpace.modulePullbackDerived i.toShHom ⋙ tensorRight (normalShift i) ⟶ rHomOD where
  app K := comparisonApp i rHomOD rHomODAdjunction structureSheafUnitIso
    normalIdentification K
  naturality _ _ f := comparisonApp_naturality i rHomOD rHomODAdjunction
    structureSheafUnitIso normalIdentification f

/-- The component of `comparison` at `K` is the explicit effective-Cartier comparison map. -/
theorem comparison_app (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    (comparison i rHomOD rHomODAdjunction structureSheafUnitIso
      normalIdentification).app K =
        comparisonApp i rHomOD rHomODAdjunction structureSheafUnitIso
          normalIdentification K := sorry

/-- The effective-Cartier tensor-duality comparison is an isomorphism of functors. -/
instance comparisonIsIso :
    IsIso (comparison i rHomOD rHomODAdjunction structureSheafUnitIso
      normalIdentification) := sorry

end EffectiveCartierDuality

end AlgebraicGeometry.Scheme
