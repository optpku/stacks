/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.Sites
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Counit
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Module.Quasicoherent.LowerShriek

/-!
# Quasi-coherent comparison for the lisse-étale and flat-fppf sites

Inverse image and module lower shriek give equivalences on quasi-coherent
modules of an algebraic stack. On locally quasi-coherent modules with flat
base change, their composite is the quasi-coherent coreflector.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

attribute [instance] lisseEtaleModuleLowerShriek_unit_app_isIso
  flatFppfModuleLowerShriek_unit_app_isIso

namespace lisseEtaleModuleInverseImage

/-- Inverse image along the lisse-étale inclusion preserves quasi-coherence. -/
instance obj_isQuasicoherent {X : GroupoidsOver S} [AlgebraicStack X]
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) [F.IsQuasicoherent] :
    ((lisseEtaleModuleInverseImage X).obj F).IsQuasicoherent :=
  sorry

/-- If `F` is locally quasi-coherent with the flat base change property, then
`g⁻¹ F` is quasi-coherent on the lisse-étale site. -/
instance obj_isQuasicoherent_of_lqcohFbc {X : GroupoidsOver S} [AlgebraicStack X]
    (F : etaleModules X) [IsLocallyQuasiCoherent F] [HasFlatBaseChange F] :
    ((lisseEtaleModuleInverseImage X).obj F).IsQuasicoherent :=
  sorry

/-- Inverse image along the lisse-étale inclusion sends the counit `Q(F) ⟶ F`
to an isomorphism. -/
instance map_toQCohCounitApp_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (F : LQCohFbc X) :
    IsIso ((lisseEtaleModuleInverseImage X).map (LQCohFbc.toQCohCounitApp F)) :=
  sorry

end lisseEtaleModuleInverseImage

namespace lisseEtaleModuleLowerShriek

/-- The counit `g_! g⁻¹ ⟶ id` is an isomorphism on quasi-coherent étale
modules. -/
instance counit_app_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (F : SheafOfModules.{u} (etaleStructureSheaf X)) [F.IsQuasicoherent] :
    IsIso ((adjunction X).counit.app F) :=
  sorry

end lisseEtaleModuleLowerShriek

namespace flatFppfModuleInverseImage

/-- Inverse image along the flat-fppf inclusion preserves quasi-coherence. -/
instance obj_isQuasicoherent {X : GroupoidsOver S} [AlgebraicStack X]
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent] :
    ((flatFppfModuleInverseImage X).obj F).IsQuasicoherent :=
  sorry

/-- If `F` is an fppf `LQCoh^{fbc}` module, then `g⁻¹ F` is quasi-coherent on
the flat-fppf site. -/
instance obj_isQuasicoherent_of_lqcohFbc {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    ((flatFppfModuleInverseImage X).obj ((FppfModules.inclusion X).obj F)).IsQuasicoherent :=
  sorry

/-- Inverse image along the flat-fppf inclusion sends the counit `Q(F) ⟶ F`
to an isomorphism. -/
instance map_toQCohCounitApp_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    IsIso ((flatFppfModuleInverseImage X).map
      (FppfModules.LQCohFbc.toQCohCounitApp F)) :=
  sorry

end flatFppfModuleInverseImage

namespace flatFppfModuleLowerShriek

/-- The counit `g_! g⁻¹ ⟶ id` is an isomorphism on quasi-coherent fppf
modules. -/
instance counit_app_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (F : SheafOfModules.{u} (structureSheaf X)) [F.IsQuasicoherent] :
    IsIso ((adjunction X).counit.app F) :=
  sorry

end flatFppfModuleLowerShriek

/-- Restriction of quasi-coherent étale modules to the lisse-étale site. -/
def lisseEtaleQCohInverseImage (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleQCoh X ⥤ lisseEtaleQCoh X :=
  (lisseEtaleQuasiCoherent X).lift
    (etaleQCoh.inclusion X ⋙ lisseEtaleModuleInverseImage X)
    (fun F ↦ lisseEtaleModuleInverseImage.obj_isQuasicoherent F.obj)

/-- Module lower shriek of quasi-coherent lisse-étale modules, landing in
quasi-coherent étale modules. -/
def lisseEtaleQCohLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleQCoh X ⥤ etaleQCoh X :=
  (etaleQuasiCoherent X).lift
    (lisseEtaleQCoh.inclusion X ⋙ lisseEtaleModuleLowerShriek X)
    (fun F ↦ lisseEtaleModuleLowerShriek.obj_isQuasicoherent F.obj)

/-- The unit isomorphism of the lisse-étale quasi-coherent equivalence, with
components the inverse of the module lower-shriek counit. -/
def lisseEtaleQCohEquivalence_unitIso (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟭 (etaleQCoh X) ≅
      lisseEtaleQCohInverseImage X ⋙ lisseEtaleQCohLowerShriek X :=
  NatIso.ofComponents
    (fun F ↦
      (etaleQuasiCoherent X).isoMk
        (asIso ((lisseEtaleModuleLowerShriek.adjunction X).counit.app F.obj)).symm)
    sorry

/-- The counit isomorphism of the lisse-étale quasi-coherent equivalence, with
components the inverse of the module lower-shriek unit. -/
def lisseEtaleQCohEquivalence_counitIso (X : GroupoidsOver S)
    [AlgebraicStack X] :
    lisseEtaleQCohLowerShriek X ⋙ lisseEtaleQCohInverseImage X ≅
      𝟭 (lisseEtaleQCoh X) :=
  NatIso.ofComponents
    (fun H ↦
      (lisseEtaleQuasiCoherent X).isoMk
        (asIso ((lisseEtaleModuleLowerShriek.adjunction X).unit.app H.obj)).symm)
    sorry

/-- The functors `g⁻¹` and `g_!` along the lisse-étale inclusion restrict to
mutually inverse equivalences between quasi-coherent étale modules and
quasi-coherent lisse-étale modules. -/
def lisseEtaleQCohEquivalence (X : GroupoidsOver S) [AlgebraicStack X] :
    etaleQCoh X ≌ lisseEtaleQCoh X :=
  CategoryTheory.Equivalence.mk (lisseEtaleQCohInverseImage X) (lisseEtaleQCohLowerShriek X)
    (lisseEtaleQCohEquivalence_unitIso X) (lisseEtaleQCohEquivalence_counitIso X)

/-- The forward functor of `lisseEtaleQCohEquivalence` is lisse-étale inverse
image on quasi-coherent modules. -/
theorem lisseEtaleQCohEquivalence_functor (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleQCohEquivalence X).functor = lisseEtaleQCohInverseImage X :=
  rfl

/-- The inverse functor of `lisseEtaleQCohEquivalence` is lisse-étale lower
shriek on quasi-coherent modules. -/
theorem lisseEtaleQCohEquivalence_inverse (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleQCohEquivalence X).inverse = lisseEtaleQCohLowerShriek X :=
  rfl

/-- Restriction of quasi-coherent fppf modules to the flat-fppf site. -/
def flatFppfQCohInverseImage (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ flatFppfQCoh X :=
  (flatFppfQuasiCoherent X).lift
    (QCoh.inclusion X ⋙ flatFppfModuleInverseImage X)
    (fun F ↦ flatFppfModuleInverseImage.obj_isQuasicoherent F.obj)

/-- Module lower shriek of quasi-coherent flat-fppf modules, landing in
quasi-coherent fppf modules. -/
def flatFppfQCohLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfQCoh X ⥤ QCoh X :=
  (quasiCoherentModuleProperty X).lift
    (flatFppfQCoh.inclusion X ⋙ flatFppfModuleLowerShriek X)
    (fun F ↦ flatFppfModuleLowerShriek.obj_isQuasicoherent F.obj)

/-- The unit isomorphism of the flat-fppf quasi-coherent equivalence, with
components the inverse of the module lower-shriek counit. -/
def flatFppfQCohEquivalence_unitIso (X : GroupoidsOver S) [AlgebraicStack X] :
    𝟭 (QCoh X) ≅ flatFppfQCohInverseImage X ⋙ flatFppfQCohLowerShriek X :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty X).isoMk
        (asIso ((flatFppfModuleLowerShriek.adjunction X).counit.app F.obj)).symm)
    sorry

/-- The counit isomorphism of the flat-fppf quasi-coherent equivalence, with
components the inverse of the module lower-shriek unit. -/
def flatFppfQCohEquivalence_counitIso (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfQCohLowerShriek X ⋙ flatFppfQCohInverseImage X ≅ 𝟭 (flatFppfQCoh X) :=
  NatIso.ofComponents
    (fun H ↦
      (flatFppfQuasiCoherent X).isoMk
        (asIso ((flatFppfModuleLowerShriek.adjunction X).unit.app H.obj)).symm)
    sorry

/-- The functors `g⁻¹` and `g_!` along the flat-fppf inclusion restrict to
mutually inverse equivalences between quasi-coherent fppf modules and
quasi-coherent flat-fppf modules. -/
def flatFppfQCohEquivalence (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ≌ flatFppfQCoh X :=
  CategoryTheory.Equivalence.mk (flatFppfQCohInverseImage X) (flatFppfQCohLowerShriek X)
    (flatFppfQCohEquivalence_unitIso X) (flatFppfQCohEquivalence_counitIso X)

/-- The forward functor of `flatFppfQCohEquivalence` is flat-fppf inverse image
on quasi-coherent modules. -/
theorem flatFppfQCohEquivalence_functor (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfQCohEquivalence X).functor = flatFppfQCohInverseImage X :=
  rfl

/-- The inverse functor of `flatFppfQCohEquivalence` is flat-fppf lower shriek
on quasi-coherent modules. -/
theorem flatFppfQCohEquivalence_inverse (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfQCohEquivalence X).inverse = flatFppfQCohLowerShriek X :=
  rfl

/-- The identification `Q(F) = g_! g⁻¹ F` on the étale site, as an isomorphism
of the underlying étale modules, built from the lisse-étale counit and the
coreflection counit. -/
def lisseEtaleToQCohIsoLowerShriekInverseImage {X : GroupoidsOver S}
    [AlgebraicStack X] (F : LQCohFbc X) :
    (LQCohFbc.inclusion X).obj ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj F)) ≅
      (lisseEtaleModuleLowerShriek X).obj
        ((lisseEtaleModuleInverseImage X).obj ((LQCohFbc.inclusion X).obj F)) :=
  (@asIso _ _ _ _
      ((lisseEtaleModuleLowerShriek.adjunction X).counit.app
        ((restriction X).obj ((LQCohFbc.toQCoh X).obj F).obj))
      (@lisseEtaleModuleLowerShriek.counit_app_isIso _ _ _ _
        (QCoh.restriction_obj_isQuasicoherent ((LQCohFbc.toQCoh X).obj F)))).symm ≪≫
    (lisseEtaleModuleLowerShriek X).mapIso
      (@asIso _ _ _ _
        ((lisseEtaleModuleInverseImage X).map (LQCohFbc.toQCohCounitApp F))
        (lisseEtaleModuleInverseImage.map_toQCohCounitApp_isIso F))

/-- The identification `Q(F) = g_! g⁻¹ F` on the fppf site, as an isomorphism of
the underlying fppf modules, built from the flat-fppf counit and the
coreflection counit. -/
def flatFppfToQCohIsoLowerShriekInverseImage {X : GroupoidsOver S}
    [AlgebraicStack X] (F : FppfModules.LQCohFbc X) :
    (QCoh.inclusion X).obj
        ((LQCohFbc.toQCoh X).obj (FppfModules.LQCohFbc.restrict F)) ≅
      (flatFppfModuleLowerShriek X).obj
        ((flatFppfModuleInverseImage X).obj ((FppfModules.inclusion X).obj F)) :=
  (@asIso _ _ _ _
      ((flatFppfModuleLowerShriek.adjunction X).counit.app
        ((LQCohFbc.toQCoh X).obj (FppfModules.LQCohFbc.restrict F)).obj)
      (flatFppfModuleLowerShriek.counit_app_isIso _)).symm ≪≫
    (flatFppfModuleLowerShriek X).mapIso
      (@asIso _ _ _ _
        ((flatFppfModuleInverseImage X).map
          (FppfModules.LQCohFbc.toQCohCounitApp F))
        (flatFppfModuleInverseImage.map_toQCohCounitApp_isIso F))

end AlgebraicGeometry.AlgebraicStack
