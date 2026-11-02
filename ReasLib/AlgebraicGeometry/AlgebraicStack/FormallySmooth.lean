/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormallySmoothOnObjects
public import ReasLib.CategoryTheory.Bicategory.DottedArrow.Construction

/-!
# Formally smooth morphisms of algebraic stacks

A morphism of algebraic stacks is formally smooth when it is formally smooth
on objects as a 1-morphism of categories fibred in groupoids.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- A morphism `f : X ⟶ Y` of algebraic stacks is formally smooth if it is
formally smooth on objects as a 1-morphism of categories fibred in groupoids. -/
@[mk_iff]
class FormallySmooth {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) : Prop
    extends Groupoids.Hom.FormallySmoothOnObjects f

namespace FormallySmooth

/-- The identity morphism of an algebraic stack is formally smooth. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] :
    FormallySmooth (𝟙 X) := by
  refine { toFormallySmoothOnObjects := ⟨?_⟩ }
  intro T T' _ _ i _ y x γ
  dsimp only [slice.pullback, slice.pullbackFunctor, Bicategory.precomp] at *
  refine ⟨y, γ.symm ≪≫ ρ_ x, ρ_ y, ?_⟩
  dsimp only [Groupoids.Hom.FormallySmoothOnObjects.restrictionSquare,
    Groupoids.Hom.FormallySmoothOnObjects.restrictHom, slice.pullback,
    slice.pullbackFunctor, Bicategory.precomp]
  simp [Category.assoc]

/-- A morphism of algebraic stacks that is formally smooth on objects is
formally smooth. -/
instance of_onObjects {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [Groupoids.Hom.FormallySmoothOnObjects f] : FormallySmooth f :=
  ⟨⟩

/-- A formally smooth morphism of algebraic stacks is formally smooth on
objects as a 1-morphism of categories fibred in groupoids. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FormallySmooth f] :
    Groupoids.Hom.FormallySmoothOnObjects f :=
  inferInstance

/-- A morphism of algebraic stacks is formally smooth if and only if every
first-order affine thickening square, with its chosen comparison isomorphism,
has a nonempty category of compatible dotted arrows. -/
@[stacks 0DNY]
theorem iff_nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    FormallySmooth f ↔
      ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
        (i : T ⟶ T') [IsFirstOrderThickening i.left]
        (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
        (γ : overMap i ≫ y ≅ x ≫ f),
        Nonempty (DottedArrow
          (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
            Bicategory.PseudoPullbackCone y f)) := by
  set_option backward.isDefEq.respectTransparency false in
    constructor
    · intro hf T T' _ _ i _ x y γ
      letI := hf
      obtain ⟨x', β, γ', h⟩ :=
        Groupoids.Hom.FormallySmoothOnObjects.exists_lift i y x γ.symm
      refine ⟨⟨x', β, γ'.symm, ?_⟩⟩
      apply Iso.ext
      change (overMap i ◁ γ'.inv) ≫
        (α_ (overMap i) x' f).inv ≫ (β.hom ▷ f) = γ.hom
      change (β.hom ▷ f) ≫ γ.inv =
        (α_ (overMap i) x' f).hom ≫ (overMap i ◁ γ'.hom) at h
      apply (cancel_mono γ.inv).1
      simp [Category.assoc, h]
      exact whiskerLeft_inv_hom (overMap i) γ'
    · intro h
      refine { toFormallySmoothOnObjects := ⟨?_⟩ }
      intro T T' _ _ i _ y x γ
      obtain ⟨A⟩ := h i x y γ.symm
      refine ⟨A.arrow, A.left, A.right.symm, ?_⟩
      have hc := congrArg Iso.hom A.comm
      change (overMap i ◁ A.right.hom) ≫
        (α_ (overMap i) A.arrow f).inv ≫ (A.left.hom ▷ f) = γ.inv at hc
      change (A.left.hom ▷ f) ≫ γ.hom =
        (α_ (overMap i) A.arrow f).hom ≫ (overMap i ◁ A.right.inv)
      apply (cancel_epi ((overMap i ◁ A.right.hom) ≫
        (α_ (overMap i) A.arrow f).inv)).1
      calc
        _ = γ.inv ≫ γ.hom := by
          simpa only [Category.assoc] using congrArg (fun k => k ≫ γ.hom) hc
        _ = _ := by
          simp [Category.assoc]
          exact (whiskerLeft_hom_inv (overMap i) A.right).symm

/-- A formally smooth morphism of algebraic stacks has a nonempty category of
dotted arrows on every first-order affine thickening square. -/
theorem nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [FormallySmooth f]
    {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
    (i : T ⟶ T') [IsFirstOrderThickening i.left]
    (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
    (γ : overMap i ≫ y ≅ x ≫ f) :
    Nonempty (DottedArrow
      (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
        Bicategory.PseudoPullbackCone y f)) :=
  (iff_nonempty_dottedArrow f).mp inferInstance i x y γ

/-- A morphism of algebraic stacks is formally smooth if every first-order
affine thickening square has a nonempty category of dotted arrows. -/
theorem of_nonempty_dottedArrow
    {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (h : ∀ {T T' : Over S} [IsAffine T.left] [IsAffine T'.left]
      (i : T ⟶ T') [IsFirstOrderThickening i.left]
      (x : GroupoidsOver.slice T ⟶ X) (y : GroupoidsOver.slice T' ⟶ Y)
      (γ : overMap i ≫ y ≅ x ≫ f),
      Nonempty (DottedArrow
        (⟨GroupoidsOver.slice T, overMap i, x, γ⟩ :
          Bicategory.PseudoPullbackCone y f))) :
    FormallySmooth f :=
  (iff_nonempty_dottedArrow f).mpr h


end FormallySmooth

end AlgebraicGeometry.AlgebraicStack
