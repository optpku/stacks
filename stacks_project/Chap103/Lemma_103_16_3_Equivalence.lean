/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap103.Lemma_103_10_1
public import stacks_project.Chap103.Lemma_103_16_3_QCoh

/-!
# Quasi-coherent restriction equivalences along lisse-étale and flat-fppf inclusions

Module inverse image `g⁻¹` and lower shriek `g_!` along the lisse-étale
(resp. flat-fppf) inclusion of an algebraic stack restrict to mutually inverse
equivalences on quasi-coherent modules. On `LQCoh^{fbc}` the same `g⁻¹` lands
in quasi-coherent modules on the small site, and the reflector `Q` of
Lemma 103.10.1 is identified with `g_! g⁻¹` by the adjunction (co)units.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Objects of `QCoh X` are quasi-coherent as fppf `𝒪_X`-modules. -/
instance QCoh.obj_isQuasicoherent {X : GroupoidsOver S} (F : QCoh X) :
    ((QCoh.inclusion X).obj F).IsQuasicoherent :=
  sorry

/-- Restriction of fppf modules to étale modules is full: morphisms of sheaves
on the identity-on-objects comparison are morphisms of the underlying
presheaves. -/
instance restriction_full (X : GroupoidsOver S) : (restriction X).Full :=
  sorry

namespace FppfModules.LQCohFbc

/-- The étale `LQCoh^{fbc}` module obtained by restricting an fppf
`LQCoh^{fbc}` module along `restriction`. -/
def restrict {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) : GroupoidsOver.LQCohFbc X :=
  ⟨(restriction X).obj F.obj, F.property⟩

/-- The underlying étale module of `restrict F` is the restriction of `F`. -/
theorem restrict_obj {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    (GroupoidsOver.LQCohFbc.inclusion X).obj (restrict F) =
      (restriction X).obj F.obj :=
  sorry

end FppfModules.LQCohFbc

namespace LQCohFbc

/-- The adjunction counit `i(Q(F)) ⟶ F` of `toLQCohFbc ⊣ toQCoh`, viewed as a
morphism of étale modules. -/
def toQCohCounitApp {X : GroupoidsOver S} [AlgebraicStack X] (F : LQCohFbc X) :
    (inclusion X).obj ((QCoh.toLQCohFbc X).obj ((toQCoh X).obj F)) ⟶
      (inclusion X).obj F :=
  (inclusion X).map ((QCoh.toLQCohFbc_isRightAdjoint_toQCoh X).some.counit.app F)

/-- The underlying étale module of `i(Q(F))` is quasi-coherent. -/
instance reflectorInclusion_isQuasicoherent {X : GroupoidsOver S}
    [AlgebraicStack X] (F : LQCohFbc X) :
    ((inclusion X).obj ((QCoh.toLQCohFbc X).obj ((toQCoh X).obj F))).IsQuasicoherent :=
  sorry

end LQCohFbc

namespace FppfModules.LQCohFbc

/-- The adjunction counit `Q(F) ⟶ F` of Lemma 103.10.1, lifted along
`restriction` to a morphism of fppf modules. -/
def toQCohCounitApp {X : GroupoidsOver S} [AlgebraicStack X]
    (F : FppfModules.LQCohFbc X) :
    (QCoh.inclusion X).obj
        ((GroupoidsOver.LQCohFbc.toQCoh X).obj (restrict F)) ⟶
      (FppfModules.inclusion X).obj F :=
  (restriction X).preimage
    (GroupoidsOver.LQCohFbc.toQCohCounitApp (restrict F))

end FppfModules.LQCohFbc

end AlgebraicGeometry.GroupoidsOver

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}}

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

/-- The unit `id ⟶ g⁻¹ g_!` is an isomorphism on every lisse-étale module. -/
instance unit_app_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (lisseEtaleStructureSheaf X)) :
    IsIso ((adjunction X).unit.app H) :=
  sorry

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

/-- The unit `id ⟶ g⁻¹ g_!` is an isomorphism on every flat-fppf module. -/
instance unit_app_isIso {X : GroupoidsOver S} [AlgebraicStack X]
    (H : SheafOfModules.{u} (flatFppfStructureSheaf X)) :
    IsIso ((adjunction X).unit.app H) :=
  sorry

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
    (etaleQCoh.inclusion X ⋙ lisseEtaleModuleInverseImage X) (fun _ ↦ sorry)

/-- Module lower shriek of quasi-coherent lisse-étale modules, landing in
quasi-coherent étale modules. -/
def lisseEtaleQCohLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    lisseEtaleQCoh X ⥤ etaleQCoh X :=
  (etaleQuasiCoherent X).lift
    (lisseEtaleQCoh.inclusion X ⋙ lisseEtaleModuleLowerShriek X) (fun _ ↦ sorry)

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
  sorry

/-- The inverse functor of `lisseEtaleQCohEquivalence` is lisse-étale lower
shriek on quasi-coherent modules. -/
theorem lisseEtaleQCohEquivalence_inverse (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (lisseEtaleQCohEquivalence X).inverse = lisseEtaleQCohLowerShriek X :=
  sorry

/-- Restriction of quasi-coherent fppf modules to the flat-fppf site. -/
def flatFppfQCohInverseImage (X : GroupoidsOver S) [AlgebraicStack X] :
    QCoh X ⥤ flatFppfQCoh X :=
  (flatFppfQuasiCoherent X).lift
    (QCoh.inclusion X ⋙ flatFppfModuleInverseImage X) (fun _ ↦ sorry)

/-- Module lower shriek of quasi-coherent flat-fppf modules, landing in
quasi-coherent fppf modules. -/
def flatFppfQCohLowerShriek (X : GroupoidsOver S) [AlgebraicStack X] :
    flatFppfQCoh X ⥤ QCoh X :=
  (quasiCoherentModuleProperty X).lift
    (flatFppfQCoh.inclusion X ⋙ flatFppfModuleLowerShriek X) (fun _ ↦ sorry)

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
  sorry

/-- The inverse functor of `flatFppfQCohEquivalence` is flat-fppf lower shriek
on quasi-coherent modules. -/
theorem flatFppfQCohEquivalence_inverse (X : GroupoidsOver S)
    [AlgebraicStack X] :
    (flatFppfQCohEquivalence X).inverse = flatFppfQCohLowerShriek X :=
  sorry

/-- The identification `Q(F) = g_! g⁻¹ F` on the étale site, as an isomorphism
of the underlying étale modules, built from the lisse-étale counit and the
Lemma 103.10.1 counit. -/
def lisseEtaleToQCohIsoLowerShriekInverseImage {X : GroupoidsOver S}
    [AlgebraicStack X] (F : LQCohFbc X) :
    (LQCohFbc.inclusion X).obj ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj F)) ≅
      (lisseEtaleModuleLowerShriek X).obj
        ((lisseEtaleModuleInverseImage X).obj ((LQCohFbc.inclusion X).obj F)) :=
  (asIso
      ((lisseEtaleModuleLowerShriek.adjunction X).counit.app
        ((LQCohFbc.inclusion X).obj
          ((QCoh.toLQCohFbc X).obj ((LQCohFbc.toQCoh X).obj F))))).symm ≪≫
    (lisseEtaleModuleLowerShriek X).mapIso
      (asIso ((lisseEtaleModuleInverseImage X).map (LQCohFbc.toQCohCounitApp F)))

/-- The identification `Q(F) = g_! g⁻¹ F` on the fppf site, as an isomorphism of
the underlying fppf modules, built from the flat-fppf counit and the
Lemma 103.10.1 counit. -/
def flatFppfToQCohIsoLowerShriekInverseImage {X : GroupoidsOver S}
    [AlgebraicStack X] (F : FppfModules.LQCohFbc X) :
    (QCoh.inclusion X).obj
        ((LQCohFbc.toQCoh X).obj (FppfModules.LQCohFbc.restrict F)) ≅
      (flatFppfModuleLowerShriek X).obj
        ((flatFppfModuleInverseImage X).obj ((FppfModules.inclusion X).obj F)) :=
  (asIso
      ((flatFppfModuleLowerShriek.adjunction X).counit.app
        ((QCoh.inclusion X).obj
          ((LQCohFbc.toQCoh X).obj (FppfModules.LQCohFbc.restrict F))))).symm ≪≫
    (flatFppfModuleLowerShriek X).mapIso
      (asIso
        ((flatFppfModuleInverseImage X).map
          (FppfModules.LQCohFbc.toQCohCounitApp F)))

end AlgebraicGeometry.AlgebraicStack
