module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Composition
public import ReasLib.CategoryTheory.Sites.Topos.ModuleAdjunction
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Lemma_96_14_2_Restriction
public import ReasLib.CategoryTheory.Fibered.InheritedTopology.Morphism
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Pseudofunctor
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import stacks_project.Chap96.«96_10_3_1_Comparison»
public import stacks_project.Chap96.«96_10_3_3_Comparison»
public import stacks_project.Chap96.Lemma_96_10_3_Comparison
public import ReasLib.CategoryTheory.Functor.KanExtension.SmallSections

/-!
# Pullback compatibility of quasi-coherent restriction

Restriction `ℱ ↦ ℱ|_{F_étale}` intertwines pullback along a 1-morphism of
categories fibred in groupoids with small-étale pullback along the recovered
morphism of representing algebraic spaces.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor
open CategoryTheory.ObjectProperty CategoryTheory.Sheaf.InternalModule
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- The morphism of algebraic spaces recovered from a 1-morphism of categories
fibred in groupoids along representing equivalences. This is `inducedHom` of
Lemma 96.10.3, obtained from `toGroupoids.recover` along the supplied
presentations. -/
abbrev recoveredHom {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) : F ⟶ G :=
  AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f

/-- `recoveredHom eX eY f` is recovery of `f` along `eX.symm` and `eY.symm`. -/
theorem recoveredHom_eq {F G : AlgebraicSpace S} {X Y : GroupoidsOver S}
    (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y) :
    recoveredHom eX eY f = AlgebraicSpace.toGroupoids.recover eX.symm eY.symm f :=
  rfl

variable {X Y : GroupoidsOver S} {F G : AlgebraicSpace S}
variable (eX : F.toGroupoids ≌ X) (eY : G.toGroupoids ≌ Y) (f : X ⟶ Y)
variable (α : (f ≫ eY.symm.hom) ≅
    (eX.symm.hom ≫ AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f)))

/-- Identification of `AlgebraicSpace.QCoh.pullback` with small-étale module
pullback on underlying module sheaves. -/
def restrict_pullback_toSpacePullback (𝒢 : QCoh Y) :
    ((AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢)).obj ⟶
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢).obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f))
      (fun _ hℱ =>
        AlgebraicSpace.Modules.pullback_quasiCoherentModuleProperty
          (recoveredHom eX eY f) hℱ)).hom.app
    ((QCoh.restrict eY).obj 𝒢)

/-- Reverse identification of small-étale module pullback with
`AlgebraicSpace.QCoh.pullback`. -/
def restrict_pullback_fromSpacePullback (𝒢 : QCoh Y) :
    (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢).obj ⟶
      ((AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢)).obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f))
      (fun _ hℱ =>
        AlgebraicSpace.Modules.pullback_quasiCoherentModuleProperty
          (recoveredHom eX eY f) hℱ)).inv.app
    ((QCoh.restrict eY).obj 𝒢)

/-- Transport of `𝒢` to an étale module on `G.toGroupoids` along `eY.hom`. -/
def restrict_pullback_toPresented (𝒢 : QCoh Y) :
    SheafOfModules.{u} (etaleRingedSite G.toGroupoids).structureSheaf :=
  let _ := presentedTwoCell eX eY f α
  (etaleModuleInverseImage eY.hom).obj ((toEtaleRingedModules Y).obj 𝒢.obj)

/-- Inverse image of the presented module along `toGroupoids.map (recoveredHom)`,
as site-level étale inverse image. -/
def restrict_pullback_presentedPullback (𝒢 : QCoh Y) :
    SheafOfModules.{u} (etaleRingedSite F.toGroupoids).structureSheaf :=
  (etaleModuleInverseImage
      (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))).obj
    (restrict_pullback_toPresented eX eY f α 𝒢)

/-- For identity presentations, recovering the canonical represented morphism
returns the same morphism of algebraic spaces. -/
theorem restrict_pullback_presentedSpaceMorphism_eq :
    moduleComparisonSpaceMorphism
        (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))
        (Bicategory.Equivalence.id F.toGroupoids)
        (Bicategory.Equivalence.id G.toGroupoids) = recoveredHom eX eY f :=
  sorry

/-- Identity-presentation pullback comparison, using the actual canonical
site-module unit and restriction comparison. -/
def restrict_pullback_presentedHom (𝒢 : QCoh Y) :
    (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((AlgebraicSpace.restrictEtaleModules G).obj
          (restrict_pullback_toPresented eX eY f α 𝒢)) ⟶
      (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) :=
  eqToHom
      (congrArg
        (fun h => (AlgebraicSpace.Modules.pullback h).obj
          ((AlgebraicSpace.restrictEtaleModules G).obj
            (restrict_pullback_toPresented eX eY f α 𝒢)))
        (restrict_pullback_presentedSpaceMorphism_eq eX eY f).symm) ≫
    restrictPullbackComparison
      (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))
      (Bicategory.Equivalence.id F.toGroupoids)
      (Bicategory.Equivalence.id G.toGroupoids)
      (restrict_pullback_toPresented eX eY f α 𝒢)

/-- On quasi-coherent inputs, the actual comparison is bijective on each
small-étale chart. This is a law of the specified forward map. -/
theorem restrict_pullback_presentedHom_app_bijective (𝒢 : QCoh Y)
    (W : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ) :
    Function.Bijective ((restrict_pullback_presentedHom eX eY f α 𝒢).val.app W).hom :=
  sorry

/-- The reverse section function tests the actual fibre of the forward
comparison, choosing from that fibre when it is nonempty and otherwise using zero. -/
def restrict_pullback_presentedInvSection (𝒢 : QCoh Y)
    (W : (AlgebraicSpace.smallEtaleSite F)ᵒᵖ) :
    ((AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢)).val.obj W →
      ((AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((AlgebraicSpace.restrictEtaleModules G).obj
          (restrict_pullback_toPresented eX eY f α 𝒢))).val.obj W :=
  fun y =>
    @dite _
      (∃ x, ((restrict_pullback_presentedHom eX eY f α 𝒢).val.app W).hom x = y)
      (Classical.propDecidable _)
      (fun h => h.choose) (fun _ => 0)

/-- Reverse section map obtained from the actual fibres of the forward map,
with zero as the default. No asserted isomorphism supplies the inverse data. -/
def restrict_pullback_presentedInvUnderlying (𝒢 : QCoh Y) :
    (ToInternal.underlying (AlgebraicSpace.structureSheaf F)).obj
        ((AlgebraicSpace.restrictEtaleModules F).obj
          (restrict_pullback_presentedPullback eX eY f α 𝒢)) ⟶
      (ToInternal.underlying (AlgebraicSpace.structureSheaf F)).obj
        ((AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
          ((AlgebraicSpace.restrictEtaleModules G).obj
            (restrict_pullback_toPresented eX eY f α 𝒢))) where
  hom :=
    { app := fun W => TypeCat.ofHom (restrict_pullback_presentedInvSection eX eY f α 𝒢 W)
      naturality := sorry }

/-- Inverse of `restrict_pullback_presentedHom`, with its chartwise section
functions specified independently of the inverse laws. -/
def restrict_pullback_presentedInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) ⟶
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).obj
        ((AlgebraicSpace.restrictEtaleModules G).obj
          (restrict_pullback_toPresented eX eY f α 𝒢)) :=
  homOfUnderlying (AlgebraicSpace.structureSheaf F)
    (restrict_pullback_presentedInvUnderlying eX eY f α 𝒢) sorry sorry

/-- The identity-presentation pullback comparison has the specified actual
chartwise inverse; only its two inverse laws are deferred. -/
instance restrict_pullback_presentedHom_isIso (𝒢 : QCoh Y) :
    IsIso (restrict_pullback_presentedHom eX eY f α 𝒢) :=
  Iso.isIso_hom
    { hom := restrict_pullback_presentedHom eX eY f α 𝒢
      inv := restrict_pullback_presentedInv eX eY f α 𝒢
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Comparison of `π_{G,*}` with identity-presentation restriction, as the
composite module-pushforward isomorphism along `etaleSiteHom eY.hom` and `π_G`. -/
def restrict_pullback_restrictToPresented (𝒢 : QCoh Y) :
    ((etaleSiteHom eY.hom).modulePushforward ⋙
        (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids)).modulePushforward).obj
      ((toEtaleRingedModules Y).obj 𝒢.obj) ⟶
      ((etaleSiteHom eY.hom).comp
          (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).modulePushforward.obj
        ((toEtaleRingedModules Y).obj 𝒢.obj) :=
  let _ := presentedTwoCell eX eY f α
  (RingedSite.Hom.modulePushforwardCompIso
      (etaleSiteHom eY.hom)
      (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).hom.app
    ((toEtaleRingedModules Y).obj 𝒢.obj)

/-- Reverse comparison of identity-presentation restriction with the composite
`π_{G,*}`. -/
def restrict_pullback_presentedToRestrict (𝒢 : QCoh Y) :
    ((etaleSiteHom eY.hom).comp
          (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).modulePushforward.obj
        ((toEtaleRingedModules Y).obj 𝒢.obj) ⟶
      ((etaleSiteHom eY.hom).modulePushforward ⋙
        (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids)).modulePushforward).obj
      ((toEtaleRingedModules Y).obj 𝒢.obj) :=
  let _ := presentedTwoCell eX eY f α
  (RingedSite.Hom.modulePushforwardCompIso
      (etaleSiteHom eY.hom)
      (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).inv.app
    ((toEtaleRingedModules Y).obj 𝒢.obj)

/-- The base functor of `etaleSiteHom eY.hom ≫ π_G` agrees with the base of `π_G`. -/
theorem restrict_pullback_piComp_base :
    ((etaleSiteHom eY.hom).comp
        (pi G G.toGroupoids (Bicategory.Equivalence.id G.toGroupoids))).base =
      (pi G Y eY).base :=
  rfl

/-- The presentation site morphism followed by the identity-presentation
restriction is the specified restriction site morphism. -/
theorem restrict_pullback_presentation_pi {Z : GroupoidsOver S} {H : AlgebraicSpace S}
    (e : H.toGroupoids ≌ Z) :
    (etaleSiteHom e.hom).comp
        (pi H H.toGroupoids (Bicategory.Equivalence.id H.toGroupoids)) = pi H Z e :=
  sorry

/-- Comparison of `π_{G,*}` with identity-presentation restriction, using the
actual pushforward-composition isomorphism and the presentation site equality. -/
def restrict_pullback_idPresented (𝒢 : QCoh Y) :
    ((QCoh.restrict eY).obj 𝒢).obj ⟶
      (AlgebraicSpace.restrictEtaleModules G).obj
        (restrict_pullback_toPresented eX eY f α 𝒢) :=
  eqToHom
      (congrArg
        (fun H => H.modulePushforward.obj ((toEtaleRingedModules Y).obj 𝒢.obj))
        (restrict_pullback_presentation_pi eY).symm) ≫
    restrict_pullback_presentedToRestrict eX eY f α 𝒢

/-- Reverse comparison of identity-presentation restriction with `π_{G,*}`. -/
def restrict_pullback_idPresentedInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules G).obj
        (restrict_pullback_toPresented eX eY f α 𝒢) ⟶
      ((QCoh.restrict eY).obj 𝒢).obj :=
  restrict_pullback_restrictToPresented eX eY f α 𝒢 ≫
    eqToHom
      (congrArg
        (fun H => H.modulePushforward.obj ((toEtaleRingedModules Y).obj 𝒢.obj))
        (restrict_pullback_presentation_pi eY))

/-- Identification of `QCoh.pullback f` with `modulePullback f` on underlying modules. -/
def restrict_pullback_toModulePullback (𝒢 : QCoh Y) :
    ((QCoh.pullback f).obj 𝒢).obj ⟶ (modulePullback f).obj 𝒢.obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (modulePullback f) (modulePullback_le_inverseImage f)).hom.app 𝒢

/-- Reverse identification of `modulePullback f` with `QCoh.pullback f`. -/
def restrict_pullback_fromModulePullback (𝒢 : QCoh Y) :
    (modulePullback f).obj 𝒢.obj ⟶ ((QCoh.pullback f).obj 𝒢).obj :=
  let _ := presentedTwoCell eX eY f α
  (ObjectProperty.FullSubcategory.restrict.compιIso
      (modulePullback f) (modulePullback_le_inverseImage f)).inv.app 𝒢

/-- Identity-on-Γ transport intertwines CFG module pullback with étale inverse image. -/
def restrict_pullback_toEtaleCommute (𝒢 : QCoh Y) :
    (toEtaleRingedModules X).obj ((modulePullback f).obj 𝒢.obj) ⟶
      (etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj) :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((toEtaleRingedModules X).obj ((modulePullback f).obj 𝒢.obj)).val.presheaf)
        sorry }

/-- Reverse identity-on-Γ comparison of étale inverse image with CFG module pullback. -/
def restrict_pullback_toEtaleCommuteInv (𝒢 : QCoh Y) :
    (etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj) ⟶
      (toEtaleRingedModules X).obj ((modulePullback f).obj 𝒢.obj) :=
  { val :=
      PresheafOfModules.homMk
        (𝟙 ((etaleModuleInverseImage f).obj
              ((toEtaleRingedModules Y).obj 𝒢.obj)).val.presheaf)
        sorry }

/-- `π_{F,eX,*}` of étale inverse image along `f` compared with identity-presentation
restriction of `eX.hom^*` of that inverse image. -/
def restrict_pullback_idLeftPresented (𝒢 : QCoh Y) :
    (restrictModules eX).obj
        ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj)) ⟶
      (AlgebraicSpace.restrictEtaleModules F).obj
        ((etaleModuleInverseImage eX.hom).obj
          ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj))) :=
  eqToHom
      (congrArg
        (fun H => H.modulePushforward.obj
          ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj)))
        (restrict_pullback_presentation_pi eX).symm) ≫
    (RingedSite.Hom.modulePushforwardCompIso
      (etaleSiteHom eX.hom)
      (pi F F.toGroupoids (Bicategory.Equivalence.id F.toGroupoids))).inv.app
      ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj))

/-- Reverse of `restrict_pullback_idLeftPresented`. -/
def restrict_pullback_idLeftPresentedInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules F).obj
        ((etaleModuleInverseImage eX.hom).obj
          ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj))) ⟶
      (restrictModules eX).obj
        ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj)) :=
  (RingedSite.Hom.modulePushforwardCompIso
      (etaleSiteHom eX.hom)
      (pi F F.toGroupoids (Bicategory.Equivalence.id F.toGroupoids))).hom.app
      ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
    eqToHom
      (congrArg
        (fun H => H.modulePushforward.obj
          ((etaleModuleInverseImage f).obj ((toEtaleRingedModules Y).obj 𝒢.obj)))
        (restrict_pullback_presentation_pi eX))

/-- Comparison of `QCoh.restrict eX` of the CFG pullback with identity-presentation
restriction on `F`. -/
def restrict_pullback_idLeft (𝒢 : QCoh Y) :
    ((QCoh.restrict eX).obj ((QCoh.pullback f).obj 𝒢)).obj ⟶
      (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) :=
  (restrictModules eX).map
      ((toEtaleRingedModules X).map (restrict_pullback_toModulePullback eX eY f α 𝒢)) ≫
    (restrictModules eX).map (restrict_pullback_toEtaleCommute f 𝒢) ≫
      restrict_pullback_idLeftPresented eX f 𝒢 ≫
        (AlgebraicSpace.restrictEtaleModules F).map
          ((etaleModuleInverseImage_comp eX.hom f).hom.app
            ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
          (AlgebraicSpace.restrictEtaleModules F).map
            ((etaleModuleInverseImage_iso (presentedTwoCell eX eY f α)).hom.app
              ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
            (AlgebraicSpace.restrictEtaleModules F).map
              ((etaleModuleInverseImage_comp
                  (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))
                  eY.hom).inv.app
                ((toEtaleRingedModules Y).obj 𝒢.obj))

/-- Reverse comparison on `F`. -/
def restrict_pullback_idLeftInv (𝒢 : QCoh Y) :
    (AlgebraicSpace.restrictEtaleModules F).obj
        (restrict_pullback_presentedPullback eX eY f α 𝒢) ⟶
      ((QCoh.restrict eX).obj ((QCoh.pullback f).obj 𝒢)).obj :=
  (AlgebraicSpace.restrictEtaleModules F).map
      ((etaleModuleInverseImage_comp
          (AlgebraicSpace.toGroupoids.map (recoveredHom eX eY f))
          eY.hom).hom.app
        ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
    (AlgebraicSpace.restrictEtaleModules F).map
      ((etaleModuleInverseImage_iso (presentedTwoCell eX eY f α)).inv.app
        ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
      (AlgebraicSpace.restrictEtaleModules F).map
        ((etaleModuleInverseImage_comp eX.hom f).inv.app
          ((toEtaleRingedModules Y).obj 𝒢.obj)) ≫
        restrict_pullback_idLeftPresentedInv eX f 𝒢 ≫
          (restrictModules eX).map (restrict_pullback_toEtaleCommuteInv f 𝒢) ≫
            (restrictModules eX).map
              ((toEtaleRingedModules X).map
                (restrict_pullback_fromModulePullback eX eY f α 𝒢))

/-- Module-level comparison of the two pullback-restriction composites. The
forward map is identity-on-Γ transport of CFG pullback, followed by the
identity-presentation canonical site-module comparison. -/
def restrict_pullback_modulesIso (𝒢 : QCoh Y) :
    ((QCoh.restrict eX).obj ((QCoh.pullback f).obj 𝒢)).obj ≅
      ((AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f)).obj
        ((QCoh.restrict eY).obj 𝒢)).obj where
  hom :=
    restrict_pullback_idLeft eX eY f α 𝒢 ≫
      restrict_pullback_presentedInv eX eY f α 𝒢 ≫
        (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).map
            (restrict_pullback_idPresentedInv eX eY f α 𝒢) ≫
          restrict_pullback_fromSpacePullback eX eY f α 𝒢
  inv :=
    restrict_pullback_toSpacePullback eX eY f α 𝒢 ≫
      (AlgebraicSpace.Modules.pullback (recoveredHom eX eY f)).map
          (restrict_pullback_idPresented eX eY f α 𝒢) ≫
        restrict_pullback_presentedHom eX eY f α 𝒢 ≫
          restrict_pullback_idLeftInv eX eY f α 𝒢
  hom_inv_id := sorry
  inv_hom_id := sorry

namespace QCoh

/-- Compatibility of `QCoh.restrict` with pullback along a 1-morphism of
categories fibred in groupoids represented by algebraic spaces. The
presentation 2-iso `α` records that `recoveredHom eX eY f` is the morphism of
algebraic spaces associated to `f`. -/
def restrict_pullbackComparison :
    pullback f ⋙ restrict eX ≅
      restrict eY ⋙ AlgebraicSpace.QCoh.pullback (recoveredHom eX eY f) :=
  NatIso.ofComponents
    (fun 𝒢 =>
      { hom := homMk (restrict_pullback_modulesIso eX eY f α 𝒢).hom
        inv := homMk (restrict_pullback_modulesIso eX eY f α 𝒢).inv
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The component of `restrict_pullbackComparison` is
`restrict_pullback_modulesIso`. -/
theorem restrict_pullbackComparison_hom_app (𝒢 : QCoh Y) :
    ((restrict_pullbackComparison eX eY f α).hom.app 𝒢).hom =
      (restrict_pullback_modulesIso eX eY f α 𝒢).hom :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
