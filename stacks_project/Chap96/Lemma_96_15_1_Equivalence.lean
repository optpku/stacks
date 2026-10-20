/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.LocalEquivalence
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.Equivalence
public import stacks_project.Chap94.Definition_94_16_5_Presentation
public import stacks_project.Chap96.Lemma_96_13_2
public import stacks_project.Chap96.Proposition_96_14_3

/-!
# Presentation equivalence on quasi-coherent modules

A presentation `[U / R] ⟶ 𝒳` of an algebraic stack induces a canonical
equivalence `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)`, obtained by pulling back along
the presenting `1`-morphism and applying the quotient-stack comparison.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack CategoryTheory
  CategoryTheory.Functor CategoryTheory.ObjectProperty
  FiberedCategoryOver.Groupoids AlgebraicGeometry.GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]

/-- The presenting `1`-morphism of a presentation is an equivalence over `Over S`. -/
instance presentation_hom_isEquivalence (P : Presentation X) :
    (toBasedFunctor P.hom).IsEquivalence :=
  P.isEquivalence

/-- The underlying based functor of `toCartesianBasedFunctor P.hom` is an
equivalence because it agrees with `toBasedFunctor P.hom`. -/
instance presentation_hom_cartesian_isEquivalence (P : Presentation X) :
    (toCartesianBasedFunctor P.hom).toBasedFunctor.IsEquivalence :=
  (toCartesianBasedFunctor.toBasedFunctor P.hom).symm ▸ P.isEquivalence

/-- The chosen quasi-inverse `1`-morphism of a presentation, obtained from the
based inverse of `P.hom`. -/
def presentationInvHom (P : Presentation X) : X ⟶ P.groupoid.quotientStack :=
  ofBasedFunctor (toBasedFunctor P.hom).inv

/-- `presentationInvHom` is `ofBasedFunctor` of the based inverse of `P.hom`. -/
theorem presentationInvHom_eq (P : Presentation X) :
    presentationInvHom P = ofBasedFunctor (toBasedFunctor P.hom).inv :=
  sorry

/-- Pullback of quasi-coherent modules along a presenting equivalence is an
equivalence of categories. -/
instance pullback_hom_isEquivalence (P : Presentation X) :
    (pullback P.hom).IsEquivalence :=
  pullback_isEquivalence P.hom
    (CartesianBasedFunctor.IsLocalEquivalence.of_isEquivalence
      (Scheme.fppfTopology.over S) (toCartesianBasedFunctor P.hom))

/-- The forward functor of the presentation equivalence, sending a
quasi-coherent module on `𝒳` to the corresponding equivariant module on
`(U, R, s, t, c)`. -/
def presentationFunctor (P : Presentation X) : QCoh X ⥤ P.groupoid.QCoh :=
  pullback P.hom ⋙ toGroupoid P.groupoid

/-- `presentationFunctor` is pullback along `P.hom` followed by `toGroupoid`. -/
theorem presentationFunctor_eq (P : Presentation X) :
    presentationFunctor P = pullback P.hom ⋙ toGroupoid P.groupoid :=
  sorry

/-- The inverse functor of the presentation equivalence, sending an equivariant
module on `(U, R, s, t, c)` to a quasi-coherent module on `𝒳`. -/
def presentationInverseFunctor (P : Presentation X) :
    P.groupoid.QCoh ⥤ QCoh X :=
  fromGroupoid P.groupoid ⋙ pullback (presentationInvHom P)

/-- `presentationInverseFunctor` is `fromGroupoid` followed by pullback along
`presentationInvHom`. -/
theorem presentationInverseFunctor_eq (P : Presentation X) :
    presentationInverseFunctor P =
      fromGroupoid P.groupoid ⋙ pullback (presentationInvHom P) :=
  sorry

/-- The composite `presentationInvHom ≫ P.hom` is isomorphic to the identity of
`𝒳`, via the based counit of `P.hom`. -/
def presentationInvHom_comp_hom (P : Presentation X) :
    presentationInvHom P ≫ P.hom ≅ 𝟙 X :=
  BasedFunctorIso.lift <|
    eqToIso
        (rfl :
          toBasedFunctor (presentationInvHom P ≫ P.hom) =
            BasedFunctor.comp (toBasedFunctor (presentationInvHom P))
              (toBasedFunctor P.hom)) ≪≫
      eqToIso
        (congrArg (fun F ↦ BasedFunctor.comp F (toBasedFunctor P.hom))
          (rfl :
            toBasedFunctor (presentationInvHom P) =
              (toBasedFunctor P.hom).inv)) ≪≫
      (toBasedFunctor P.hom).counitIso ≪≫
        eqToIso (rfl : 𝟙 X.toBasedCategory = toBasedFunctor (𝟙 X))

/-- The composite `P.hom ≫ presentationInvHom` is isomorphic to the identity of
the quotient stack, via the based unit of `P.hom`. -/
def hom_comp_presentationInvHom (P : Presentation X) :
    P.hom ≫ presentationInvHom P ≅ 𝟙 P.groupoid.quotientStack :=
  BasedFunctorIso.lift <|
    eqToIso
        (rfl :
          toBasedFunctor (P.hom ≫ presentationInvHom P) =
            BasedFunctor.comp (toBasedFunctor P.hom)
              (toBasedFunctor (presentationInvHom P))) ≪≫
      eqToIso
        (congrArg (fun G ↦ BasedFunctor.comp (toBasedFunctor P.hom) G)
          (rfl :
            toBasedFunctor (presentationInvHom P) =
              (toBasedFunctor P.hom).inv)) ≪≫
      (toBasedFunctor P.hom).unitIso.symm ≪≫
        eqToIso
          (rfl :
            𝟙 P.groupoid.quotientStack.toBasedCategory =
              toBasedFunctor (𝟙 P.groupoid.quotientStack))

/-- Pullback along `presentationInvHom ≫ P.hom` is pullback along `P.hom` after
pullback along `presentationInvHom`. -/
def pullback_presentationInvHom_comp_hom (P : Presentation X) :
    pullback (presentationInvHom P ≫ P.hom) ≅
      pullback P.hom ⋙ pullback (presentationInvHom P) :=
  pullback_comp (presentationInvHom P) P.hom

/-- Pullback along `P.hom ≫ presentationInvHom` is pullback along
`presentationInvHom` after pullback along `P.hom`. -/
def pullback_hom_comp_presentationInvHom (P : Presentation X) :
    pullback (P.hom ≫ presentationInvHom P) ≅
      pullback (presentationInvHom P) ⋙ pullback P.hom :=
  pullback_comp P.hom (presentationInvHom P)

/-- The coefficient morphism of the identity 1-morphism is the identity of the
structure sheaf. -/
theorem structureSheafMap_id (Y : GroupoidsOver S) :
    structureSheafMap (𝟙 Y) = 𝟙 (structureSheaf Y) :=
  sorry

/-- Inverse image of modules along the identity 1-morphism is the identity
functor. The comparison is identity-on-sections restriction of scalars along the
definitional identity coefficient, not an `eqToIso` of a sorry module equality. -/
def modulePullback_id (Y : GroupoidsOver S) :
    modulePullback (𝟙 Y) ≅ 𝟭 (SheafOfModules.{u} (structureSheaf Y)) :=
  SheafOfModules.pushforwardCongr
      (rfl : structureSheafMap (𝟙 Y) = 𝟙 (structureSheaf Y)) ≪≫
    SheafOfModules.pushforwardId (R := structureSheaf Y)

/-- Pullback along the identity of `𝒳` is isomorphic to the identity functor of
`QCoh 𝒳`. -/
def pullback_id (Y : GroupoidsOver S) : pullback (𝟙 Y) ≅ 𝟭 (QCoh Y) :=
  NatIso.ofComponents
    (fun F ↦
      (quasiCoherentModuleProperty Y).isoMk
        ((FullSubcategory.restrict.compιIso (modulePullback (𝟙 Y))
            (modulePullback_le_inverseImage (𝟙 Y))).app F ≪≫
          (modulePullback_id Y).app F.obj))
    sorry

/-- Pullback along `P.hom` followed by pullback along `presentationInvHom` is
isomorphic to the identity of `QCoh 𝒳`. -/
def pullback_hom_invHom (P : Presentation X) :
    pullback P.hom ⋙ pullback (presentationInvHom P) ≅ 𝟭 (QCoh X) :=
  (pullback_presentationInvHom_comp_hom P).symm ≪≫
    (pullbackIso (presentationInvHom_comp_hom P)).symm ≪≫
      pullback_id X

/-- Pullback along `presentationInvHom` followed by pullback along `P.hom` is
isomorphic to the identity of `QCoh` of the quotient stack. -/
def pullback_invHom_hom (P : Presentation X) :
    pullback (presentationInvHom P) ⋙ pullback P.hom ≅
      𝟭 (QCoh P.groupoid.quotientStack) :=
  (pullback_hom_comp_presentationInvHom P).symm ≪≫
    (pullbackIso (hom_comp_presentationInvHom P)).symm ≪≫
      pullback_id P.groupoid.quotientStack

/-- Unit identification of `presentationFunctor` followed by
`presentationInverseFunctor`. -/
def presentationEquivalence_unitIso (P : Presentation X) :
    𝟭 (QCoh X) ≅ presentationFunctor P ⋙ presentationInverseFunctor P :=
  (pullback_hom_invHom P).symm ≪≫
    isoWhiskerRight (isoWhiskerLeft (pullback P.hom)
        (toGroupoidEquivalence_unitIso P.groupoid))
      (pullback (presentationInvHom P)) ≪≫
      (Functor.associator (pullback P.hom) (toGroupoid P.groupoid)
          (fromGroupoid P.groupoid ⋙ pullback (presentationInvHom P))).symm ≪≫
        isoWhiskerLeft (pullback P.hom)
          (Functor.associator (toGroupoid P.groupoid) (fromGroupoid P.groupoid)
            (pullback (presentationInvHom P))) ≪≫
          Functor.associator (pullback P.hom)
            (toGroupoid P.groupoid ⋙ fromGroupoid P.groupoid)
            (pullback (presentationInvHom P))

/-- Counit identification of `presentationInverseFunctor` followed by
`presentationFunctor`. -/
def presentationEquivalence_counitIso (P : Presentation X) :
    presentationInverseFunctor P ⋙ presentationFunctor P ≅ 𝟭 P.groupoid.QCoh :=
  (Functor.associator (fromGroupoid P.groupoid)
      (pullback (presentationInvHom P)) (presentationFunctor P)).symm ≪≫
    isoWhiskerLeft (fromGroupoid P.groupoid)
      ((Functor.associator (pullback (presentationInvHom P)) (pullback P.hom)
          (toGroupoid P.groupoid)).symm ≪≫
        isoWhiskerRight (pullback_invHom_hom P) (toGroupoid P.groupoid) ≪≫
          (toGroupoid P.groupoid).leftUnitor) ≪≫
      toGroupoidEquivalence_counitIso P.groupoid

/-- Canonical equivalence `QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` associated to a
presentation of an algebraic stack. -/
def presentationEquivalence (P : Presentation X) : QCoh X ≌ P.groupoid.QCoh :=
  CategoryTheory.Equivalence.mk (presentationFunctor P)
    (presentationInverseFunctor P) (presentationEquivalence_unitIso P)
    (presentationEquivalence_counitIso P)

/-- The forward functor of `presentationEquivalence` is `presentationFunctor`. -/
theorem presentationEquivalence_functor (P : Presentation X) :
    (presentationEquivalence P).functor = presentationFunctor P :=
  sorry

/-- The inverse of `presentationEquivalence` is `presentationInverseFunctor`. -/
theorem presentationEquivalence_inverse (P : Presentation X) :
    (presentationEquivalence P).inverse = presentationInverseFunctor P :=
  sorry

end AlgebraicGeometry.GroupoidsOver.QCoh
