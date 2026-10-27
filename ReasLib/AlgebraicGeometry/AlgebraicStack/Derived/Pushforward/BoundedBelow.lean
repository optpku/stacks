/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Derived.Pushforward
public import ReasLib.CategoryTheory.DerivedCategory.Functor.TotalRightDerived.Homotopy.BoundedBelow
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Degree.InjectiveResolution
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated
public import ReasLib.CategoryTheory.ObjectProperty.FullSubcategory.Restriction

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
open CategoryTheory.Functor CategoryTheory.ObjectProperty AlgebraicGeometry.GroupoidsOver
open DerivedCategory DerivedCategory.TStructure
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

-- Local instance justification (defeq pin): the homotopy localization must use the Abelian and induced additive structures of the fppf module presentation in ModuleDerived.
attribute [local instance 2000] GroupoidsOver.fppfModulesAbelian
  Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms fppfModulesHasDerivedCategory

-- Local instance justification (defeq pin): ModuleDerived uses this standard localization through fppfModulesHasDerivedCategory, at the same module-category universe.
attribute [local instance 1900] HasDerivedCategory.standard

-- Local instance justification (defeq pin): homotopy-to-derived direct image must select the canonical additivity certificate for the concrete fppf module direct image.
attribute [local instance 2000] instFppfModulePushforwardAdditive

variable {S : Scheme.{u}}

/-- Bounded-below module pushforward admits a total right derived functor. -/
instance fppfModulePushforwardHasBoundedRightDerived
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) :
    (fppfModulePushforward f).toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso (fppfModules X)) := sorry

/-- Homotopy-to-derived module pushforward has a pointwise right derived
functor at quasi-isomorphisms. -/
instance fppfModulePushforwardHasPointwiseRightDerived
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (Homotopy.toDerived (fppfModulePushforward f)).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (fppfModules X) (ComplexShape.up ℤ)) := sorry

-- Local instance justification (defeq pin): the canonical derived functor explicitly uses this ordinary-derivability certificate; pointwise existence must not select another model.
attribute [local instance 2000] fppfModulePushforwardHasRightDerived

/-- Unbounded `Rf_*` commutes with shifts. -/
instance moduleDerivedPushforward.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (moduleDerivedPushforward f).CommShift ℤ :=
  totalRightDerived_commShift
    (Homotopy.toDerived (fppfModulePushforward f))
    (HomotopyCategory.quasiIso (fppfModules X) (ComplexShape.up ℤ))
    (DerivedCategory.Qh :
      HomotopyCategory (fppfModules X) (ComplexShape.up ℤ) ⥤
        DerivedCategory (fppfModules X))

/-- Unbounded `Rf_*` is triangulated. -/
instance moduleDerivedPushforward.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    (moduleDerivedPushforward f).IsTriangulated := sorry

/-- Unbounded derived pushforward preserves bounded-below objects. -/
theorem mapsTo_plus {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    :
    (t.plus : ObjectProperty (ModuleDerived X)) ≤
      (t.plus : ObjectProperty (ModuleDerived Y)).inverseImage
        (moduleDerivedPushforward f) := sorry

/-- Bounded-below restriction of unbounded `Rf_*`. -/
def moduleDerivedPushforwardPlus {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    :
    Plus (fppfModules X) ⥤ Plus (fppfModules Y) :=
  FullSubcategory.restrict (moduleDerivedPushforward f) (mapsTo_plus f)

/-- Inclusion comparison for the bounded-below restriction of `Rf_*`. -/
def moduleDerivedPushforwardPlus_comp_ι {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    :
    moduleDerivedPushforwardPlus f ⋙ Plus.ι ≅
      Plus.ι ⋙ moduleDerivedPushforward f :=
  FullSubcategory.restrict.compιIso (moduleDerivedPushforward f) (mapsTo_plus f)

set_option backward.isDefEq.respectTransparency false in
/-- Bounded-below `Rf_*` commutes with shifts. -/
instance moduleDerivedPushforwardPlus.instCommShift {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    :
    (moduleDerivedPushforwardPlus f).CommShift ℤ :=
  Functor.CommShift.ofComp (moduleDerivedPushforwardPlus_comp_ι f) ℤ

/-- Bounded-below `Rf_*` is triangulated. -/
instance moduleDerivedPushforwardPlus.instIsTriangulated {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    :
    (moduleDerivedPushforwardPlus f).IsTriangulated := sorry

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack

-- Local instance justification (defeq pin): the homotopy localization must use the Abelian and induced additive structures of the fppf module presentation in ModuleDerived.
attribute [local instance 2000] GroupoidsOver.fppfModulesAbelian
  Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms fppfModulesHasDerivedCategory

-- Local instance justification (defeq pin): ModuleDerived uses this standard localization through fppfModulesHasDerivedCategory, at the same module-category universe.
attribute [local instance 1900] HasDerivedCategory.standard

-- Local instance justification (defeq pin): homotopy-to-derived direct image must select the canonical additivity certificate for the concrete fppf module direct image.
attribute [local instance 2000] instFppfModulePushforwardAdditive

variable {S : Scheme.{u}}

/-- Degree-`i` homology of bounded-below fppf `Rf_*` on a degree-zero object is
the ordinary right-derived functor of module pushforward. -/
def moduleDerivedPushforwardPlus.singleHomologyIso {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (i : ℕ) :
    DerivedCategory.Plus.singleFunctor (fppfModules X) 0 ⋙
        moduleDerivedPushforwardPlus f ⋙
          DerivedCategory.Plus.homologyFunctor (fppfModules Y) (i : ℤ) ≅
      (fppfModulePushforward f).rightDerived i :=
  (isoWhiskerRight
      (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (fppfModules X) 0)
        (moduleDerivedPushforwardPlus_comp_ι f))
      (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ))) ≪≫
    (isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (fppfModules X) 0)
      (isoWhiskerRight
        (Functor.RightDerived.Homotopy.BoundedBelow.canonicalModelIso
          (fppfModulePushforward f)).symm
        (DerivedCategory.homologyFunctor (fppfModules Y) (i : ℤ)))) ≪≫
    Functor.RightDerived.Bounded.degree.degreeFunctorIsoRightDerived
      (fppfModulePushforward f) i

end AlgebraicGeometry.AlgebraicStack
