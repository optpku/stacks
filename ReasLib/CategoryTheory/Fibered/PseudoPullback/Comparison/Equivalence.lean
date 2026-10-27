/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
-- `FiberedCategory.Fibered` supplies the Cartesian lifts used by the explicit inverse.
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Functor.Equivalence
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Comparison.Functor
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Iso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Symmetry.Equivalence
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Equivalences.Swap

/-!
# Fibred comparison equivalences for explicit pseudo-pullbacks

The deterministic comparison functor is owned by `PseudoPullback.Comparison.Functor`. This leaf
constructs its inverse by lifting the right component along the displayed base isomorphism.
The left-fibred version follows by the two explicit swap equivalences. Their equivalence
properties and base-projection comparisons are derived from these data.
-/

@[expose] public section

universe v u vX uX vY uY vZ uZ

namespace CategoryTheory

open BasedCategory
open CategoryTheory.Limits
open CategoricalPullback
open Functor
open scoped CategoricalPullback

variable {C : Type u} [Category.{v} C]
variable {X : BasedCategory.{vX, uX} C}
variable {Y : BasedCategory.{vY, uY} C}
variable {Z : BasedCategory.{vZ, uZ} C}

namespace BasedCategory.PseudoPullback.Comparison

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace Implementation

variable (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)

/-- The base isomorphism of an ordinary pullback object, transported along the stored
projection equations of the two based functors. -/
private def baseIso (P : F.toFunctor ⊡ G.toFunctor) :
    X.p.obj P.fst ≅ Y.p.obj P.snd :=
  (eqToIso (F.w_obj P.fst)).symm ≪≫ Z.p.mapIso P.iso ≪≫ eqToIso (G.w_obj P.snd)

variable [Y.p.IsFibered]

/-- The right component pulled back along its displayed base isomorphism. The only choice is
mathlib's Cartesian lift, whose existence is supplied by the fibredness input. -/
private noncomputable def rightObj (P : F.toFunctor ⊡ G.toFunctor) : Y.obj :=
  IsPreFibered.pullbackObj (p := Y.p) rfl (baseIso F G P).hom

private noncomputable def rightHom (P : F.toFunctor ⊡ G.toFunctor) :
    rightObj F G P ⟶ P.snd :=
  IsPreFibered.pullbackMap (p := Y.p) rfl (baseIso F G P).hom

/-- A Cartesian lift of an isomorphism is an isomorphism. This certificate uses only
mathlib's proved lifting theorem and the fibredness parameter. -/
private theorem rightHom_isIso (P : F.toFunctor ⊡ G.toFunctor) :
    IsIso (rightHom F G P) := by
  letI : Y.p.IsCartesian (baseIso F G P).hom (rightHom F G P) :=
    IsPreFibered.pullbackMap.IsCartesian rfl (baseIso F G P).hom
  exact IsStronglyCartesian.isIso_of_base_isIso Y.p (baseIso F G P).hom (rightHom F G P)

private noncomputable def rightIso (P : F.toFunctor ⊡ G.toFunctor) :
    rightObj F G P ≅ P.snd :=
  letI := rightHom_isIso F G P
  asIso (rightHom F G P)

private theorem rightObj_proj (P : F.toFunctor ⊡ G.toFunctor) :
    Y.p.obj (rightObj F G P) = X.p.obj P.fst :=
  IsPreFibered.pullbackObj_proj rfl (baseIso F G P).hom

/-- The comparison after replacing the right component is vertical. -/
private theorem inverseObj_vertical (P : F.toFunctor ⊡ G.toFunctor) :
    Z.p.IsHomLift (𝟙 (X.p.obj P.fst))
      (P.iso ≪≫ (G.toFunctor.mapIso (rightIso F G P)).symm).hom := sorry

private noncomputable def inverseObj (P : F.toFunctor ⊡ G.toFunctor) :
    (PseudoPullback F G).obj :=
  PseudoPullback.mk F G (X.p.obj P.fst)
    { fst := ⟨P.fst, rfl⟩
      snd := ⟨rightObj F G P, rightObj_proj F G P⟩
      iso := Functor.Fiber.isoMk
        (P.iso ≪≫ (G.toFunctor.mapIso (rightIso F G P)).symm)
        (inverseObj_vertical F G P) }

private theorem inverseMap_snd_lift {P Q : F.toFunctor ⊡ G.toFunctor} (φ : P ⟶ Q) :
    Y.p.IsHomLift (X.p.map φ.fst)
      ((rightIso F G P).hom ≫ φ.snd ≫ (rightIso F G Q).inv) := sorry

private theorem inverseMap_comm {P Q : F.toFunctor ⊡ G.toFunctor} (φ : P ⟶ Q) :
    CommSq (F.toFunctor.map φ.fst)
      (PseudoPullback.comparison (inverseObj F G P))
      (PseudoPullback.comparison (inverseObj F G Q))
      (G.toFunctor.map ((rightIso F G P).hom ≫ φ.snd ≫ (rightIso F G Q).inv)) := sorry

private noncomputable def inverseMap {P Q : F.toFunctor ⊡ G.toFunctor} (φ : P ⟶ Q) :
    inverseObj F G P ⟶ inverseObj F G Q :=
  PseudoPullback.Hom.mk (X.p.map φ.fst) φ.fst (IsHomLift.map X.p φ.fst)
    ((rightIso F G P).hom ≫ φ.snd ≫ (rightIso F G Q).inv)
    (inverseMap_snd_lift F G φ) (inverseMap_comm F G φ)

private noncomputable def inverse :
    F.toFunctor ⊡ G.toFunctor ⥤ (PseudoPullback F G).obj where
  obj := inverseObj F G
  map := inverseMap F G
  map_id := by intros; sorry
  map_comp := by intros; sorry

private theorem counitApp_comm (P : F.toFunctor ⊡ G.toFunctor) :
    F.toFunctor.map (𝟙 P.fst) ≫ P.iso.hom =
      ((functor F G).obj (inverseObj F G P)).iso.hom ≫
        G.toFunctor.map (rightIso F G P).hom := sorry

private noncomputable def counitApp (P : F.toFunctor ⊡ G.toFunctor) :
    (inverse F G ⋙ functor F G).obj P ≅ P :=
  CategoricalPullback.mkIso (Iso.refl P.fst) (rightIso F G P) (counitApp_comm F G P)

private noncomputable def counitIso : inverse F G ⋙ functor F G ≅ 𝟭 _ :=
  NatIso.ofComponents (counitApp F G) (by intros; sorry)

private theorem unitApp_fst_lift (P : (PseudoPullback F G).obj) :
    X.p.IsHomLift (PseudoPullback.fstBaseIso P).inv
      (𝟙 (PseudoPullback.fstObj P)) := sorry

private theorem unitApp_snd_lift (P : (PseudoPullback F G).obj) :
    Y.p.IsHomLift (PseudoPullback.fstBaseIso P).inv
      (rightIso F G ((functor F G).obj P)).inv := sorry

private theorem unitApp_comm (P : (PseudoPullback F G).obj) :
    CommSq (F.toFunctor.map (𝟙 (PseudoPullback.fstObj P)))
      (PseudoPullback.comparison P)
      (PseudoPullback.comparison ((functor F G ⋙ inverse F G).obj P))
      (G.toFunctor.map (rightIso F G ((functor F G).obj P)).inv) := sorry

private noncomputable def unitApp (P : (PseudoPullback F G).obj) :
    P ≅ (functor F G ⋙ inverse F G).obj P :=
  PseudoPullback.mkIso (PseudoPullback.fstBaseIso P).symm
    (Iso.refl (PseudoPullback.fstObj P)) (rightIso F G ((functor F G).obj P)).symm
    (unitApp_fst_lift F G P) (unitApp_snd_lift F G P) (unitApp_comm F G P)

private noncomputable def unitIso : 𝟭 _ ≅ functor F G ⋙ inverse F G :=
  NatIso.ofComponents (unitApp F G) (by intros; sorry)

end Implementation

/-- When the right source is fibred, the explicit same-fiber pseudo-pullback is canonically
equivalent, as a category, to the ordinary categorical pullback of the underlying functors. -/
@[stacks 0H2E]
noncomputable def equivalence
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (PseudoPullback F G).obj ≌ F.toFunctor ⊡ G.toFunctor :=
  CategoryTheory.Equivalence.mk (functor F G) (Implementation.inverse F G)
    (Implementation.unitIso F G) (Implementation.counitIso F G)

/-- The canonical comparison functor is an equivalence when the right source projection is
fibred, as witnessed by the explicit lifted-component inverse. -/
instance functor.isEquivalence
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (functor F G).IsEquivalence :=
  (equivalence F G).isEquivalence_functor

/-- The inverse retains the first object and uses its base as the common base. -/
@[simp]
theorem equivalence.inverse.obj.base
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : F.toFunctor ⊡ G.toFunctor) :
    PseudoPullback.baseObj ((equivalence F G).inverse.obj P) = X.p.obj P.fst := rfl

/-- The inverse retains the first object. -/
@[simp]
theorem equivalence.inverse.obj.fst
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : F.toFunctor ⊡ G.toFunctor) :
    PseudoPullback.fstObj ((equivalence F G).inverse.obj P) = P.fst := rfl

/-- The right component of the inverse is the Cartesian lift along the original base
isomorphism, with its full lifting specification supplied by mathlib. -/
@[simp]
theorem equivalence.inverse.obj.snd
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : F.toFunctor ⊡ G.toFunctor) :
    PseudoPullback.sndObj ((equivalence F G).inverse.obj P) =
      IsPreFibered.pullbackObj (p := Y.p) rfl (Implementation.baseIso F G P).hom := rfl

/-- The inverse retains the first component of every morphism. -/
@[simp]
theorem equivalence.inverse.map.fst
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : F.toFunctor ⊡ G.toFunctor} (φ : P ⟶ Q) :
    PseudoPullback.fstMap ((equivalence F G).inverse.map φ) = φ.fst := rfl

/-- The right morphism is conjugated by the two specified Cartesian-lift isomorphisms. -/
@[simp]
theorem equivalence.inverse.map.snd
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z)
    {P Q : F.toFunctor ⊡ G.toFunctor} (φ : P ⟶ Q) :
    PseudoPullback.sndMap ((equivalence F G).inverse.map φ) =
      (Implementation.rightIso F G P).hom ≫ φ.snd ≫
        (Implementation.rightIso F G Q).inv := rfl

/-- The forward functor of the selected right-fibred comparison equivalence is the deterministic
comparison functor. -/
@[simp]
theorem equivalence.functor
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).functor = functor F G := rfl

/-- The forward functor of the right-fibred comparison equivalence is compatible with the first
base projection. This is the universe-polymorphic transport of `fstBaseIso` across
`equivalence.functor`. -/
noncomputable def equivalence.functor.fstBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).functor ⋙
        (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalence.functor F G))
      (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.fstBaseIso F G

/-- The forward functor of the right-fibred comparison equivalence is compatible with the second
base projection. This is the universe-polymorphic transport of `sndBaseIso` across
`equivalence.functor`. -/
noncomputable def equivalence.functor.sndBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).functor ⋙
        (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalence.functor F G))
      (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.sndBaseIso F G

namespace Implementation

/-- Swapping twice gives the explicit ordinary equivalence of the two based pullbacks. -/
private noncomputable def swapEquivalence (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (PseudoPullback F G).obj ≌ (PseudoPullback G F).obj :=
  CategoryTheory.Equivalence.mk
    (PseudoPullback.swap F G).toFunctor (PseudoPullback.swap G F).toFunctor
    (BasedNatIso.toNatIso (PseudoPullback.swap.involution.iso F G)).symm
    (BasedNatIso.toNatIso (PseudoPullback.swap.involution.iso G F))

private noncomputable def leftEquivalence [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (PseudoPullback F G).obj ≌ F.toFunctor ⊡ G.toFunctor :=
  (swapEquivalence F G).trans
    ((equivalence G F).trans (CategoricalPullback.swap.equivalence G.toFunctor F.toFunctor))

private theorem leftComparisonApp_comm [X.p.IsFibered]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    F.toFunctor.map (𝟙 (PseudoPullback.fstObj P)) ≫ ((functor F G).obj P).iso.hom =
      ((leftEquivalence F G).functor.obj P).iso.hom ≫
        G.toFunctor.map (𝟙 (PseudoPullback.sndObj P)) := sorry

private noncomputable def leftComparisonApp [X.p.IsFibered]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) (P : (PseudoPullback F G).obj) :
    (leftEquivalence F G).functor.obj P ≅ (functor F G).obj P :=
  CategoricalPullback.mkIso (Iso.refl _) (Iso.refl _) (leftComparisonApp_comm F G P)

private noncomputable def leftComparisonIso [X.p.IsFibered]
    (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (leftEquivalence F G).functor ≅ functor F G :=
  NatIso.ofComponents (leftComparisonApp F G) (by intros; sorry)

end Implementation

/-- When the left source is fibred, swap the legs, apply the right-fibred equivalence, and
swap back. The forward comparison uses its explicit identity-component identification. -/
@[stacks 0H2E "left-fibred pseudo-pullback comparison equivalence"]
noncomputable def equivalenceOfLeft
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (PseudoPullback F G).obj ≌ F.toFunctor ⊡ G.toFunctor :=
  (Implementation.leftEquivalence F G).changeFunctor (Implementation.leftComparisonIso F G)

/-- The canonical comparison functor is also an equivalence when the left source projection is
fibred. This symmetric proposition-level entry point is not registered as an instance, avoiding
overlapping typeclass paths when both sources are fibred. -/
theorem functor.isEquivalenceOfLeft
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (functor F G).IsEquivalence :=
  (equivalenceOfLeft F G).isEquivalence_functor

/-- The forward functor of the selected left-fibred comparison equivalence is the deterministic
comparison functor. -/
@[simp]
theorem equivalenceOfLeft.functor
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).functor = functor F G := rfl

/-- The forward functor of the left-fibred comparison equivalence is compatible with the first
base projection. -/
noncomputable def equivalenceOfLeft.functor.fstBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).functor ⋙
        (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalenceOfLeft.functor F G))
      (π₁ F.toFunctor G.toFunctor ⋙ X.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.fstBaseIso F G

/-- The forward functor of the left-fibred comparison equivalence is compatible with the second
base projection. -/
noncomputable def equivalenceOfLeft.functor.sndBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).functor ⋙
        (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≅
      (PseudoPullback F G).p :=
  Functor.isoWhiskerRight (eqToIso (equivalenceOfLeft.functor F G))
      (π₂ F.toFunctor G.toFunctor ⋙ Y.p) ≪≫
    CategoryTheory.BasedCategory.PseudoPullback.Comparison.sndBaseIso F G

/-- Inverse form of the left projection compatibility for the right-fibred selected equivalence. -/
noncomputable def equivalence.inverse.fstBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₁ F.toFunctor G.toFunctor ⋙ X.p :=
  Iso.inverseCompIso
    (equivalence.functor.fstBaseIso F G).symm

/-- Inverse form of the right projection compatibility for the right-fibred selected
equivalence. -/
noncomputable def equivalence.inverse.sndBaseIso
    [Y.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalence F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₂ F.toFunctor G.toFunctor ⋙ Y.p :=
  Iso.inverseCompIso
    (equivalence.functor.sndBaseIso F G).symm

/-- Inverse form of the left projection compatibility for the left-fibred selected
equivalence. -/
noncomputable def equivalenceOfLeft.inverse.fstBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₁ F.toFunctor G.toFunctor ⋙ X.p :=
  Iso.inverseCompIso
    (equivalenceOfLeft.functor.fstBaseIso F G).symm

/-- Inverse form of the right projection compatibility for the left-fibred selected
equivalence. -/
noncomputable def equivalenceOfLeft.inverse.sndBaseIso
    [X.p.IsFibered] (F : X ⥤ᵇ Z) (G : Y ⥤ᵇ Z) :
    (equivalenceOfLeft F G).inverse ⋙
        (PseudoPullback F G).p ≅
      π₂ F.toFunctor G.toFunctor ⋙ Y.p :=
  Iso.inverseCompIso
    (equivalenceOfLeft.functor.sndBaseIso F G).symm

end BasedCategory.PseudoPullback.Comparison

end CategoryTheory
