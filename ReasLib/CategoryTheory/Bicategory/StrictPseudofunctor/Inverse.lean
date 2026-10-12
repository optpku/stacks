/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.Naturality.PointwiseEquivalence.Equivalence
public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.WeakInverse.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Strict inverses of strict pseudofunctors

This module owns the equality-level inverse certificate for strict pseudofunctors.
It is deliberately independent of any particular bicategory of stacks.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory.Bicategory
open scoped CategoryTheory.Bicategory CategoryTheory.Pseudofunctor.StrongTrans

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.StrictPseudofunctor

/-- An equality-level certificate that two strict pseudofunctors are mutually inverse on
objects, `1`-morphisms, and `2`-morphisms.

This strict presentation is useful when a construction is computationally inverse.  It is
stronger than a bicategorical equivalence, whose general owner uses strong transformations and
invertible modifications. -/
structure IsStrictInverse
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    (F : StrictPseudofunctor B D) (G : StrictPseudofunctor D B) : Prop where
  /-- The composite `G.obj ∘ F.obj` is strictly the identity on objects. -/
  left_obj : ∀ X : B, G.obj (F.obj X) = X
  /-- The composite `G.map ∘ F.map` is heterogeneously the identity on `1`-morphisms. -/
  left_map : ∀ ⦃X Y : B⦄ (f : X ⟶ Y), G.map (F.map f) ≍ f
  /-- The composite `G.map₂ ∘ F.map₂` is heterogeneously the identity on `2`-morphisms. -/
  left_map₂ : ∀ ⦃X Y : B⦄ {f g : X ⟶ Y} (η : f ⟶ g), G.map₂ (F.map₂ η) ≍ η
  /-- The composite `F.obj ∘ G.obj` is strictly the identity on objects. -/
  right_obj : ∀ X : D, F.obj (G.obj X) = X
  /-- The composite `F.map ∘ G.map` is heterogeneously the identity on `1`-morphisms. -/
  right_map : ∀ ⦃X Y : D⦄ (f : X ⟶ Y), F.map (G.map f) ≍ f
  /-- The composite `F.map₂ ∘ G.map₂` is heterogeneously the identity on `2`-morphisms. -/
  right_map₂ : ∀ ⦃X Y : D⦄ {f g : X ⟶ Y} (η : f ⟶ g), F.map₂ (G.map₂ η) ≍ η

/-- Reversing an equality-level inverse certificate exchanges the two strict
pseudofunctors. -/
theorem IsStrictInverse.symm
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}
    (h : IsStrictInverse F G) : IsStrictInverse G F := sorry

/-- Compose equality-level strict inverse certificates. The inverse of the composite is the
reverse composite of the selected strict inverses. -/
theorem IsStrictInverse.comp
    {A : Type u₁} [Bicategory.{w₁, v₁} A]
    {B : Type u₂} [Bicategory.{w₂, v₂} B]
    {C : Type u₃} [Bicategory.{w₃, v₃} C]
    {F : StrictPseudofunctor A B} {G : StrictPseudofunctor B A}
    {H : StrictPseudofunctor B C} {K : StrictPseudofunctor C B}
    (hFG : IsStrictInverse F G) (hHK : IsStrictInverse H K) :
    IsStrictInverse (F.comp H) (K.comp G) := sorry

/-- A strict pseudofunctor admitting an equality-level strict inverse is a biequivalence after
forgetting strictness. -/
theorem IsStrictInverse.leftIsBiequivalence
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}
    (h : IsStrictInverse F G) :
    Pseudofunctor.IsBiequivalence F.toPseudofunctor := sorry

/-- The chosen strict inverse in an equality-level inverse certificate is itself a
biequivalence after forgetting strictness. -/
theorem IsStrictInverse.rightIsBiequivalence
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}
    (h : IsStrictInverse F G) :
    Pseudofunctor.IsBiequivalence G.toPseudofunctor := sorry

namespace IsStrictInverse

variable
    {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {D : Type u₂} [Bicategory.{w₂, v₂} D]
    {F : StrictPseudofunctor B D} {G : StrictPseudofunctor D B}

/-- The object component of the comparison from `F` followed by `G` to the identity. -/
def leftApp (h : IsStrictInverse F G) (X : B) :
    (F.toPseudofunctor.comp G.toPseudofunctor).obj X ⟶
      (Pseudofunctor.id B).obj X :=
  eqToHom (h.left_obj X)

/-- Naturality equality for the left strict-inverse comparison. -/
theorem leftNaturality
    (h : IsStrictInverse F G) {X Y : B} (f : X ⟶ Y) :
    (F.toPseudofunctor.comp G.toPseudofunctor).map f ≫ leftApp h Y =
      leftApp h X ≫ (Pseudofunctor.id B).map f := sorry

/-- Naturality isomorphism for the left strict-inverse comparison. -/
def leftNaturalityIso
    (h : IsStrictInverse F G) {X Y : B} (f : X ⟶ Y) :
    (F.toPseudofunctor.comp G.toPseudofunctor).map f ≫ leftApp h Y ≅
      leftApp h X ≫ (Pseudofunctor.id B).map f :=
  eqToIso (leftNaturality h f)

/-- Modification naturality for the left strict-inverse comparison. -/
private theorem leftNaturalityNaturality
    (h : IsStrictInverse F G) {X Y : B} {f g : X ⟶ Y} (eta : f ⟶ g) :
    (F.toPseudofunctor.comp G.toPseudofunctor).map₂ eta ▷ leftApp h Y ≫
        (leftNaturalityIso h g).hom =
      (leftNaturalityIso h f).hom ≫
        leftApp h X ◁ (Pseudofunctor.id B).map₂ eta := sorry

/-- Identity coherence for the left strict-inverse comparison. -/
private theorem leftNaturalityId
    (h : IsStrictInverse F G) (X : B) :
    (leftNaturalityIso h (𝟙 X)).hom ≫
        leftApp h X ◁ ((Pseudofunctor.id B).mapId X).hom =
      ((F.toPseudofunctor.comp G.toPseudofunctor).mapId X).hom ▷ leftApp h X ≫
        (λ_ (leftApp h X)).hom ≫ (ρ_ (leftApp h X)).inv := sorry

/-- Composition coherence for the left strict-inverse comparison. -/
private theorem leftNaturalityComp
    (h : IsStrictInverse F G) {X Y Z : B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (leftNaturalityIso h (f ≫ g)).hom ≫
        leftApp h X ◁ ((Pseudofunctor.id B).mapComp f g).hom =
      ((F.toPseudofunctor.comp G.toPseudofunctor).mapComp f g).hom ▷ leftApp h Z ≫
        (α_ _ _ _).hom ≫
        (F.toPseudofunctor.comp G.toPseudofunctor).map f ◁
          (leftNaturalityIso h g).hom ≫
        (α_ _ _ _).inv ≫
        (leftNaturalityIso h f).hom ▷ (Pseudofunctor.id B).map g ≫
        (α_ _ _ _).hom := sorry

/-- The strong transformation from `F` followed by `G` to the identity determined by a strict
inverse certificate. -/
def leftTransformation (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans
      (F.toPseudofunctor.comp G.toPseudofunctor) (Pseudofunctor.id B) where
  app := leftApp h
  naturality := leftNaturalityIso h
  naturality_naturality := leftNaturalityNaturality h
  naturality_id := leftNaturalityId h
  naturality_comp := leftNaturalityComp h

/-- The naturality isomorphism of the left strict-inverse transformation is the canonical
isomorphism induced by `leftNaturality`. -/
@[simp]
theorem leftTransformation.naturality
    (h : IsStrictInverse F G) {X Y : B} (f : X ⟶ Y) :
    (leftTransformation h).naturality f = leftNaturalityIso h f := sorry

/-- The component of the left strict-inverse transformation is the equality-induced
`1`-morphism from the strict object comparison. -/
@[simp]
theorem leftTransformation.app (h : IsStrictInverse F G) (X : B) :
    (leftTransformation h).app X = eqToHom (h.left_obj X) := sorry

/-- Pointwise adjoint-equivalence data on the left strict-inverse transformation. -/
def leftPointwiseEquivalence (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (leftTransformation h) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun X ↦ Bicategory.eqToEquivalence (h.left_obj X))
    (fun X ↦ eqToIso ((Bicategory.eqToEquivalence.hom (h.left_obj X)).trans
      (leftTransformation.app h X).symm))

/-- The inverse component chosen by the left pointwise equivalence is the equality-induced
inverse of the strict object comparison. -/
@[simp]
theorem leftPointwiseEquivalence.invApp (h : IsStrictInverse F G) (X : B) :
    (leftPointwiseEquivalence h).invApp X = eqToHom (h.left_obj X).symm := sorry

/-- The equivalence from `F` followed by `G` to the identity determined by a strict inverse
certificate. -/
def leftEquivalence (h : IsStrictInverse F G) :
    F.toPseudofunctor.comp G.toPseudofunctor ≌ Pseudofunctor.id B :=
  (leftPointwiseEquivalence h).toEquivalence

/-- The forward transformation of the left equivalence is the canonical strict-inverse
comparison. -/
@[simp]
theorem leftEquivalence.hom (h : IsStrictInverse F G) :
    (leftEquivalence h).hom = leftTransformation h := sorry

/-- The forward component of the left equivalence is induced by strict object equality. -/
@[simp]
theorem leftEquivalence.hom.app (h : IsStrictInverse F G) (X : B) :
    (leftEquivalence h).hom.app X = eqToHom (h.left_obj X) := sorry

/-- The inverse component of the left equivalence is induced by reversed strict object
equality. -/
@[simp]
theorem leftEquivalence.inv.app (h : IsStrictInverse F G) (X : B) :
    (leftEquivalence h).inv.app X = eqToHom (h.left_obj X).symm := sorry

/-- The object component of the comparison from `G` followed by `F` to the identity. -/
def rightApp (h : IsStrictInverse F G) (X : D) :
    (G.toPseudofunctor.comp F.toPseudofunctor).obj X ⟶
      (Pseudofunctor.id D).obj X :=
  eqToHom (h.right_obj X)

/-- Naturality equality for the right strict-inverse comparison. -/
theorem rightNaturality
    (h : IsStrictInverse F G) {X Y : D} (f : X ⟶ Y) :
    (G.toPseudofunctor.comp F.toPseudofunctor).map f ≫ rightApp h Y =
      rightApp h X ≫ (Pseudofunctor.id D).map f := sorry

/-- Naturality isomorphism for the right strict-inverse comparison. -/
def rightNaturalityIso
    (h : IsStrictInverse F G) {X Y : D} (f : X ⟶ Y) :
    (G.toPseudofunctor.comp F.toPseudofunctor).map f ≫ rightApp h Y ≅
      rightApp h X ≫ (Pseudofunctor.id D).map f :=
  eqToIso (rightNaturality h f)

/-- Modification naturality for the right strict-inverse comparison. -/
private theorem rightNaturalityNaturality
    (h : IsStrictInverse F G) {X Y : D} {f g : X ⟶ Y} (eta : f ⟶ g) :
    (G.toPseudofunctor.comp F.toPseudofunctor).map₂ eta ▷ rightApp h Y ≫
        (rightNaturalityIso h g).hom =
      (rightNaturalityIso h f).hom ≫
        rightApp h X ◁ (Pseudofunctor.id D).map₂ eta := sorry

/-- Identity coherence for the right strict-inverse comparison. -/
private theorem rightNaturalityId
    (h : IsStrictInverse F G) (X : D) :
    (rightNaturalityIso h (𝟙 X)).hom ≫
        rightApp h X ◁ ((Pseudofunctor.id D).mapId X).hom =
      ((G.toPseudofunctor.comp F.toPseudofunctor).mapId X).hom ▷ rightApp h X ≫
        (λ_ (rightApp h X)).hom ≫ (ρ_ (rightApp h X)).inv := sorry

/-- Composition coherence for the right strict-inverse comparison. -/
private theorem rightNaturalityComp
    (h : IsStrictInverse F G) {X Y Z : D} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (rightNaturalityIso h (f ≫ g)).hom ≫
        rightApp h X ◁ ((Pseudofunctor.id D).mapComp f g).hom =
      ((G.toPseudofunctor.comp F.toPseudofunctor).mapComp f g).hom ▷ rightApp h Z ≫
        (α_ _ _ _).hom ≫
        (G.toPseudofunctor.comp F.toPseudofunctor).map f ◁
          (rightNaturalityIso h g).hom ≫
        (α_ _ _ _).inv ≫
        (rightNaturalityIso h f).hom ▷ (Pseudofunctor.id D).map g ≫
        (α_ _ _ _).hom := sorry

/-- The strong transformation from `G` followed by `F` to the identity determined by a strict
inverse certificate. -/
def rightTransformation (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans
      (G.toPseudofunctor.comp F.toPseudofunctor) (Pseudofunctor.id D) where
  app := rightApp h
  naturality := rightNaturalityIso h
  naturality_naturality := rightNaturalityNaturality h
  naturality_id := rightNaturalityId h
  naturality_comp := rightNaturalityComp h

/-- The naturality isomorphism of the right strict-inverse transformation is the canonical
isomorphism induced by `rightNaturality`. -/
@[simp]
theorem rightTransformation.naturality
    (h : IsStrictInverse F G) {X Y : D} (f : X ⟶ Y) :
    (rightTransformation h).naturality f = rightNaturalityIso h f := sorry

/-- The component of the right strict-inverse transformation is the equality-induced
`1`-morphism from the strict object comparison. -/
@[simp]
theorem rightTransformation.app (h : IsStrictInverse F G) (X : D) :
    (rightTransformation h).app X = eqToHom (h.right_obj X) := sorry

/-- Pointwise adjoint-equivalence data on the right strict-inverse transformation. -/
def rightPointwiseEquivalence (h : IsStrictInverse F G) :
    Pseudofunctor.StrongTrans.PointwiseEquivalence (rightTransformation h) :=
  Pseudofunctor.StrongTrans.PointwiseEquivalence.ofComponents
    (fun X ↦ Bicategory.eqToEquivalence (h.right_obj X))
    (fun X ↦ eqToIso ((Bicategory.eqToEquivalence.hom (h.right_obj X)).trans
      (rightTransformation.app h X).symm))

/-- The inverse component chosen by the right pointwise equivalence is the equality-induced
inverse of the strict object comparison. -/
@[simp]
theorem rightPointwiseEquivalence.invApp (h : IsStrictInverse F G) (X : D) :
    (rightPointwiseEquivalence h).invApp X = eqToHom (h.right_obj X).symm := sorry

/-- The equivalence from `G` followed by `F` to the identity determined by a strict inverse
certificate. -/
def rightEquivalence (h : IsStrictInverse F G) :
    G.toPseudofunctor.comp F.toPseudofunctor ≌ Pseudofunctor.id D :=
  (rightPointwiseEquivalence h).toEquivalence

/-- The forward transformation of the right equivalence is the canonical strict-inverse
comparison. -/
@[simp]
theorem rightEquivalence.hom (h : IsStrictInverse F G) :
    (rightEquivalence h).hom = rightTransformation h := sorry

/-- The forward component of the right equivalence is induced by strict object equality. -/
@[simp]
theorem rightEquivalence.hom.app (h : IsStrictInverse F G) (X : D) :
    (rightEquivalence h).hom.app X = eqToHom (h.right_obj X) := sorry

/-- The inverse component of the right equivalence is induced by reversed strict object
equality. -/
@[simp]
theorem rightEquivalence.inv.app (h : IsStrictInverse F G) (X : D) :
    (rightEquivalence h).inv.app X = eqToHom (h.right_obj X).symm := sorry

/-- Promote an equality-level strict inverse certificate to explicit weak-inverse data. -/
def toWeakInverse (h : IsStrictInverse F G) :
    Pseudofunctor.WeakInverse F.toPseudofunctor G.toPseudofunctor where
  left := leftEquivalence h
  right := rightEquivalence h

/-- The left equivalence stored by `toWeakInverse` is the canonical left strict-inverse
equivalence. -/
@[simp]
theorem toWeakInverse.left (h : IsStrictInverse F G) :
    (toWeakInverse h).left = leftEquivalence h := sorry

/-- The right equivalence stored by `toWeakInverse` is the canonical right strict-inverse
equivalence. -/
@[simp]
theorem toWeakInverse.right (h : IsStrictInverse F G) :
    (toWeakInverse h).right = rightEquivalence h := sorry

/-- The forward component of the left equivalence stored by `toWeakInverse` is induced by the
left strict object equality. -/
@[simp]
theorem toWeakInverse.left.hom.app (h : IsStrictInverse F G) (X : B) :
    (toWeakInverse h).left.hom.app X = eqToHom (h.left_obj X) := sorry

/-- The inverse component of the left equivalence stored by `toWeakInverse` is induced by the
reversed left strict object equality. -/
@[simp]
theorem toWeakInverse.left.inv.app (h : IsStrictInverse F G) (X : B) :
    (toWeakInverse h).left.inv.app X = eqToHom (h.left_obj X).symm := sorry

/-- The forward component of the right equivalence stored by `toWeakInverse` is induced by the
right strict object equality. -/
@[simp]
theorem toWeakInverse.right.hom.app (h : IsStrictInverse F G) (X : D) :
    (toWeakInverse h).right.hom.app X = eqToHom (h.right_obj X) := sorry

/-- The inverse component of the right equivalence stored by `toWeakInverse` is induced by the
reversed right strict object equality. -/
@[simp]
theorem toWeakInverse.right.inv.app (h : IsStrictInverse F G) (X : D) :
    (toWeakInverse h).right.inv.app X = eqToHom (h.right_obj X).symm := sorry

end IsStrictInverse

end CategoryTheory.StrictPseudofunctor
