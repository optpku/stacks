/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.TopologyTransport
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.RestrictionAdjunction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.SpaceComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.QuasicoherentRestriction
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Pullback

/-! # Quasi-coherent modules on a represented category fibred in groupoids -/

@[expose] public section

set_option backward.privateInPublic true

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
  CategoryTheory.ObjectProperty Opposite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {F : AlgebraicSpace S} {X : GroupoidsOver S}

/-- Restriction to a representing algebraic space preserves quasi-coherence. -/
theorem restrict_le (e : F.toGroupoids ≌ X) :
    quasiCoherentModuleProperty X ≤
      (AlgebraicSpace.quasiCoherentModuleProperty F).inverseImage
        (GroupoidsOver.toEtaleModules X ⋙ restrictModules e) := by
  sorry

/-- The module inverse image from the representing small étale site, followed
by fppf sheafification, preserves quasi-coherence. -/
theorem piStar_le (e : F.toGroupoids ≌ X) :
    AlgebraicSpace.quasiCoherentModuleProperty F ≤
      (quasiCoherentModuleProperty X).inverseImage
        (PiModulePullback.left e ⋙ fromEtaleModules X) := by
  sorry

private def inverseSection {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (y : N) : M := by
  classical
  exact if h : ∃ x, f x = y then h.choose else 0

private theorem inverseSection_left {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Bijective f) :
    Function.LeftInverse (inverseSection f) f := by
  intro x
  dsimp [inverseSection]
  rw [dif_pos ⟨x, rfl⟩]
  exact hf.1 (Exists.choose_spec (⟨x, rfl⟩ : ∃ y, f y = f x))

private theorem inverseSection_right {R : Type u} [Ring R]
    {M N : ModuleCat.{u} R} (f : M ⟶ N) (hf : Function.Bijective f) :
    Function.RightInverse (inverseSection f) f := by
  intro y
  dsimp [inverseSection]
  rw [dif_pos (hf.2 y)]
  exact Exists.choose_spec (hf.2 y)

private def inverseModuleHom {C : Type (u + 1)} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ x, Function.Bijective (f.val.app x)) : N ⟶ M where
  val :=
    { app x := ModuleCat.ofHom
        ((f.val.app x).hom.inverse (inverseSection (f.val.app x))
          (inverseSection_left _ (hf x)) (inverseSection_right _ (hf x)))
      naturality := by
        intro x y a
        ext s
        apply (hf y).1
        change (f.val.app y) (inverseSection (f.val.app y) ((N.val.map a) s)) =
          (f.val.app y) ((M.val.map a) (inverseSection (f.val.app x) s))
        rw [inverseSection_right _ (hf y), PresheafOfModules.naturality_apply,
          inverseSection_right _ (hf x)] }

namespace QCoh

/-- Restriction of quasi-coherent modules to a representing small étale site. -/
def restrict (e : F.toGroupoids ≌ X) : QCoh X ⥤ AlgebraicSpace.QCoh F :=
  (AlgebraicSpace.quasiCoherentModuleProperty F).lift
    (inclusion X ⋙ GroupoidsOver.toEtaleModules X ⋙ restrictModules e)
    (fun M => restrict_le e M.obj M.property)

/-- Restriction is the canonical topology transport followed by module restriction. -/
theorem restrict_obj (e : F.toGroupoids ≌ X) (M : QCoh X) :
    ((restrict e).obj M).obj =
      (restrictModules e).obj ((GroupoidsOver.toEtaleModules X).obj M.obj) := rfl

/-- Inverse image from the representing small étale site followed by fppf sheafification. -/
def piStar (e : F.toGroupoids ≌ X) : AlgebraicSpace.QCoh F ⥤ QCoh X :=
  (quasiCoherentModuleProperty X).lift
    (AlgebraicSpace.QCoh.inclusion F ⋙ PiModulePullback.left e ⋙ fromEtaleModules X)
    (fun M => piStar_le e M.obj M.property)

/-- The underlying module of the quasi-coherent inverse image is the concrete
small-chart inverse image followed by fppf sheafification. -/
theorem piStar_obj (e : F.toGroupoids ≌ X) (M : AlgebraicSpace.QCoh F) :
    ((piStar e).obj M).obj =
      (fromEtaleModules X).obj ((PiModulePullback.left e).obj M.obj) := rfl

/-- The restriction unit is the module adjunction unit followed by the
coefficient-transported fppf sheafification unit. -/
def restrict_piStarUnit (e : F.toGroupoids ≌ X) (M : AlgebraicSpace.QCoh F) :
    M ⟶ (restrict e).obj ((piStar e).obj M) :=
  homMk ((PiModulePullback.adjunction e).unit.app M.obj ≫
    (restrictModules e).map
      (toFromEtaleModulesComparison X ((PiModulePullback.left e).obj M.obj)))

/-- The restriction counit is the actual module adjunction counit transported
through the fppf reflection comparison. -/
def piStar_restrictCounit (e : F.toGroupoids ≌ X) (M : QCoh X) :
    (piStar e).obj ((restrict e).obj M) ⟶ M :=
  homMk ((fromEtaleModules X).map
    ((PiModulePullback.adjunction e).counit.app ((GroupoidsOver.toEtaleModules X).obj M.obj)) ≫
      (fromToEtaleModulesIso X).hom.app M.obj)

/-- The restriction unit of a quasi-coherent module is bijective on sections. -/
theorem restrict_piStarUnit_app_bijective (e : F.toGroupoids ≌ X)
    (M : AlgebraicSpace.QCoh F) (U : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ) :
    Function.Bijective ((restrict_piStarUnit e M).hom.val.app U) := by
  sorry

/-- The restriction counit of a quasi-coherent module is bijective on sections. -/
theorem piStar_restrictCounit_app_bijective (e : F.toGroupoids ≌ X)
    (M : QCoh X) (x : X.totalᵒᵖ) :
    Function.Bijective ((piStar_restrictCounit e M).hom.val.app x) := by
  sorry

/-- The inverse restriction unit selects a section in the fibre of its actual
forward linear map, with zero as the fallback on an empty fibre. -/
def restrict_piStarUnitInv (e : F.toGroupoids ≌ X) (M : AlgebraicSpace.QCoh F) :
    (restrict e).obj ((piStar e).obj M) ⟶ M :=
  homMk (inverseModuleHom (restrict_piStarUnit e M).hom
    (restrict_piStarUnit_app_bijective e M))

/-- The inverse restriction counit selects a section in the fibre of its actual
forward linear map, with zero as the fallback on an empty fibre. -/
def piStar_restrictCounitInv (e : F.toGroupoids ≌ X) (M : QCoh X) :
    M ⟶ (piStar e).obj ((restrict e).obj M) :=
  homMk (inverseModuleHom (piStar_restrictCounit e M).hom
    (piStar_restrictCounit_app_bijective e M))

/-- The specified sectionwise inverse of the restriction unit satisfies both
inverse identities. -/
theorem restrict_piStarUnitInv_laws (e : F.toGroupoids ≌ X)
    (M : AlgebraicSpace.QCoh F) :
    (restrict_piStarUnit e M ≫ restrict_piStarUnitInv e M = 𝟙 M) ∧
      (restrict_piStarUnitInv e M ≫ restrict_piStarUnit e M = 𝟙 _) := by
  sorry

/-- The specified sectionwise inverse of the restriction counit satisfies both
inverse identities. -/
theorem piStar_restrictCounitInv_laws (e : F.toGroupoids ≌ X) (M : QCoh X) :
    (piStar_restrictCounit e M ≫ piStar_restrictCounitInv e M = 𝟙 _) ∧
      (piStar_restrictCounitInv e M ≫ piStar_restrictCounit e M = 𝟙 M) := by
  sorry

/-- The canonical restriction units commute with morphisms of quasi-coherent modules. -/
theorem restrict_piStarIso_laws (e : F.toGroupoids ≌ X)
    {M N : AlgebraicSpace.QCoh F} (f : M ⟶ N) :
    f ≫ restrict_piStarUnit e N =
      restrict_piStarUnit e M ≫ (piStar e ⋙ restrict e).map f := by
  sorry

/-- The canonical restriction counits commute with morphisms of quasi-coherent modules. -/
theorem piStar_restrictIso_laws (e : F.toGroupoids ≌ X)
    {M N : QCoh X} (f : M ⟶ N) :
    (restrict e ⋙ piStar e).map f ≫ piStar_restrictCounit e N =
      piStar_restrictCounit e M ≫ f := by
  sorry

/-- Restricting the inverse image from the representing space recovers the original module. -/
def restrict_piStarIso (e : F.toGroupoids ≌ X) :
    𝟭 (AlgebraicSpace.QCoh F) ≅ piStar e ⋙ restrict e :=
  NatIso.ofComponents (fun M =>
    { hom := restrict_piStarUnit e M
      inv := restrict_piStarUnitInv e M
      hom_inv_id := (restrict_piStarUnitInv_laws e M).1
      inv_hom_id := (restrict_piStarUnitInv_laws e M).2 })
    (fun f => restrict_piStarIso_laws e f)

/-- Inverse image of the restriction recovers a quasi-coherent module on the fibration. -/
def piStar_restrictIso (e : F.toGroupoids ≌ X) :
    restrict e ⋙ piStar e ≅ 𝟭 (QCoh X) :=
  NatIso.ofComponents (fun M =>
    { hom := piStar_restrictCounit e M
      inv := piStar_restrictCounitInv e M
      hom_inv_id := (piStar_restrictCounitInv_laws e M).1
      inv_hom_id := (piStar_restrictCounitInv_laws e M).2 })
    (fun f => piStar_restrictIso_laws e f)

/-- The canonical restriction unit is invertible. -/
instance restrict_piStarUnit_isIso (e : F.toGroupoids ≌ X) (M : AlgebraicSpace.QCoh F) :
    IsIso (restrict_piStarUnit e M) where
  out := ⟨restrict_piStarUnitInv e M, restrict_piStarUnitInv_laws e M⟩

/-- The canonical restriction counit is invertible on quasi-coherent modules. -/
instance piStar_restrictCounit_isIso (e : F.toGroupoids ≌ X) (M : QCoh X) :
    IsIso (piStar_restrictCounit e M) where
  out := ⟨piStar_restrictCounitInv e M, piStar_restrictCounitInv_laws e M⟩

/-- Quasi-coherent modules on a represented category fibred in groupoids are
equivalent to quasi-coherent modules on its representing algebraic space. -/
def restrictEquivalence (e : F.toGroupoids ≌ X) : QCoh X ≌ AlgebraicSpace.QCoh F :=
  CategoryTheory.Equivalence.mk (restrict e) (piStar e)
    (piStar_restrictIso e).symm (restrict_piStarIso e).symm

/-- The forward functor of the equivalence is restriction. -/
theorem restrictEquivalence_functor (e : F.toGroupoids ≌ X) :
    (restrictEquivalence e).functor = restrict e := rfl

/-- The inverse functor of the equivalence is the specified module inverse image. -/
theorem restrictEquivalence_inverse (e : F.toGroupoids ≌ X) :
    (restrictEquivalence e).inverse = piStar e := rfl

/-- Restriction to a representing algebraic space is an equivalence. -/
instance restrict_isEquivalence (e : F.toGroupoids ≌ X) : (restrict e).IsEquivalence :=
  (restrictEquivalence e).isEquivalence_functor

variable {Y : GroupoidsOver S} {G : AlgebraicSpace S}

private def pullbackToEtaleUnderlying (f : X ⟶ Y) (M : QCoh Y) :
    ((GroupoidsOver.toEtaleModules X).obj ((modulePullback f).obj M.obj)).val.presheaf ⟶
      ((etaleModuleInverseImage f).obj ((GroupoidsOver.toEtaleModules Y).obj M.obj)).val.presheaf where
  app x := 𝟙 _
  naturality x y a := by
    ext s
    rfl

private def pullbackToEtaleInvUnderlying (f : X ⟶ Y) (M : QCoh Y) :
    ((etaleModuleInverseImage f).obj ((GroupoidsOver.toEtaleModules Y).obj M.obj)).val.presheaf ⟶
      ((GroupoidsOver.toEtaleModules X).obj ((modulePullback f).obj M.obj)).val.presheaf where
  app x := 𝟙 _
  naturality x y a := by
    ext s
    rfl

/-- Identity-on-sections topology-change comparisons for module pullback are linear. -/
theorem pullbackToEtaleComparison_laws (f : X ⟶ Y) (M : QCoh Y) :
    (∀ (x : X.totalᵒᵖ) (r : (etaleStructureSheaf X).obj.obj x)
      (m : ((GroupoidsOver.toEtaleModules X).obj ((modulePullback f).obj M.obj)).val.obj x),
      (pullbackToEtaleUnderlying f M).app x (r • m) =
        r • (pullbackToEtaleUnderlying f M).app x m) ∧
    (∀ (x : X.totalᵒᵖ) (r : (etaleStructureSheaf X).obj.obj x)
      (m : ((etaleModuleInverseImage f).obj ((GroupoidsOver.toEtaleModules Y).obj M.obj)).val.obj x),
      (pullbackToEtaleInvUnderlying f M).app x (r • m) =
        r • (pullbackToEtaleInvUnderlying f M).app x m) := by
  sorry

/-- The canonical comparison of topology transport with module pullback. -/
def pullbackToEtaleComparison (f : X ⟶ Y) (M : QCoh Y) :
    (GroupoidsOver.toEtaleModules X).obj ((modulePullback f).obj M.obj) ⟶
      (etaleModuleInverseImage f).obj ((GroupoidsOver.toEtaleModules Y).obj M.obj) where
  val := PresheafOfModules.homMk (pullbackToEtaleUnderlying f M)
    (pullbackToEtaleComparison_laws f M).1

/-- The reverse identity-on-sections comparison of topology transport with module pullback. -/
def pullbackToEtaleComparisonInv (f : X ⟶ Y) (M : QCoh Y) :
    (etaleModuleInverseImage f).obj ((GroupoidsOver.toEtaleModules Y).obj M.obj) ⟶
      (GroupoidsOver.toEtaleModules X).obj ((modulePullback f).obj M.obj) where
  val := PresheafOfModules.homMk (pullbackToEtaleInvUnderlying f M)
    (pullbackToEtaleComparison_laws f M).2

/-- Small-étale pullback of restriction maps canonically to restriction of pullback. -/
def restrictPullbackComparisonMap (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y)
    (f : X ⟶ Y) (M : QCoh Y) :
    ((restrict eY ⋙ AlgebraicSpace.QCoh.pullback
      (moduleComparisonSpaceMorphism f eX eY)).obj M) ⟶
        ((pullback f ⋙ restrict eX).obj M) :=
  homMk
    ((ObjectProperty.FullSubcategory.restrict.compιIso
      (AlgebraicSpace.Modules.pullback (moduleComparisonSpaceMorphism f eX eY))
      (fun _ h => AlgebraicSpace.Modules.pullback_quasiCoherentModuleProperty
        (moduleComparisonSpaceMorphism f eX eY) h)).hom.app ((restrict eY).obj M) ≫
      GroupoidsOver.restrictPullbackComparison f eX eY ((GroupoidsOver.toEtaleModules Y).obj M.obj) ≫
      (restrictModules eX).map
        (pullbackToEtaleComparisonInv f M ≫
          (GroupoidsOver.toEtaleModules X).map
            ((ObjectProperty.FullSubcategory.restrict.compιIso (modulePullback f)
              (modulePullback_le_inverseImage f)).inv.app M)))

/-- The direct represented-morphism comparison is bijective on sections of
quasi-coherent modules. -/
theorem restrictPullbackComparison_app_bijective
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
    (M : QCoh Y) (U : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ) :
    Function.Bijective ((restrictPullbackComparisonMap eX eY f M).hom.val.app U) := by
  sorry

/-- The inverse pullback comparison selects a section in the fibre of the
actual canonical map, using zero on an empty fibre. -/
def restrictPullbackComparisonInv
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) (M : QCoh Y) :
    ((pullback f ⋙ restrict eX).obj M) ⟶
      ((restrict eY ⋙ AlgebraicSpace.QCoh.pullback
        (moduleComparisonSpaceMorphism f eX eY)).obj M) :=
  homMk (inverseModuleHom (restrictPullbackComparisonMap eX eY f M).hom
    (restrictPullbackComparison_app_bijective eX eY f M))

/-- The specified sectionwise inverse of the direct pullback comparison satisfies
both inverse identities. -/
theorem restrictPullbackComparisonInv_laws
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) (M : QCoh Y) :
    (restrictPullbackComparisonInv eX eY f M ≫
      restrictPullbackComparisonMap eX eY f M = 𝟙 _) ∧
    (restrictPullbackComparisonMap eX eY f M ≫
      restrictPullbackComparisonInv eX eY f M = 𝟙 _) := by
  sorry

/-- The inverse direct pullback comparisons commute with morphisms of
quasi-coherent modules. -/
theorem restrictPullbackIso_laws
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
    {M N : QCoh Y} (g : M ⟶ N) :
    (pullback f ⋙ restrict eX).map g ≫ restrictPullbackComparisonInv eX eY f N =
      restrictPullbackComparisonInv eX eY f M ≫
        (restrict eY ⋙ AlgebraicSpace.QCoh.pullback
          (moduleComparisonSpaceMorphism f eX eY)).map g := by
  sorry

/-- Restriction to representing algebraic spaces intertwines pullback along
every morphism of the represented categories fibred in groupoids. -/
def restrictPullbackIso
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) :
    pullback f ⋙ restrict eX ≅
      restrict eY ⋙ AlgebraicSpace.QCoh.pullback (moduleComparisonSpaceMorphism f eX eY) :=
  NatIso.ofComponents (fun M =>
    { hom := restrictPullbackComparisonInv eX eY f M
      inv := restrictPullbackComparisonMap eX eY f M
      hom_inv_id := (restrictPullbackComparisonInv_laws eX eY f M).1
      inv_hom_id := (restrictPullbackComparisonInv_laws eX eY f M).2 })
    (fun g => restrictPullbackIso_laws eX eY f g)

/-- The inverse component of pullback compatibility is the canonical direct
represented-morphism comparison. -/
theorem restrictPullbackIso_inv_app
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) (M : QCoh Y) :
    (restrictPullbackIso eX eY f).inv.app M =
      restrictPullbackComparisonMap eX eY f M := rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
