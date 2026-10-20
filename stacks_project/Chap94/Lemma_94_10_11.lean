/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.HomPresheaf.Isom
public import ReasLib.CategoryTheory.Fibered.Representable.Slice
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import stacks_project.Chap94.Definition_94_12_1_Representable

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Diagonal
import StacksCheckRecall

/-!
# Representable diagonal of a category fibred in groupoids

The diagonal criterion is stated through its canonical shared declarations.
The seven equivalences below retain all eight equivalent conditions.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

#check (AlgebraicGeometry.isomorphismPresheaf.overLeft :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S},
    X.p.Fiber U → X.p.Fiber U → (Over U.left)ᵒᵖ ⥤ Type u)

#check (AlgebraicGeometry.isomorphismPresheaf.overLeft_eq :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    {U : Over S} (x y : X.p.Fiber U),
    isomorphismPresheaf.overLeft x y =
      U.iteratedSliceEquiv.inverse.op ⋙ Functor.isomorphismPresheaf X.p x y)

#check (AlgebraicGeometry.isomorphismPresheaf.isAlgebraicSpaceAt :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {U : Over S},
    X.p.Fiber U → X.p.Fiber U → Prop)

#check (AlgebraicGeometry.isomorphismPresheaf.isAlgebraicSpaceAt_iff :
  ∀ {S : Scheme.{u}}
    {X : GroupoidsOver S} {U : Over S} (x y : X.p.Fiber U),
    isomorphismPresheaf.isAlgebraicSpaceAt x y ↔
      ∃ F : AlgebraicSpace U.left,
        Nonempty (isomorphismPresheaf.overLeft x y ≅ F.functorOfPoints))

#check (AlgebraicGeometry.isomorphismPresheaf.isAlgebraicSpace :
  ∀ {S : Scheme.{u}}, GroupoidsOver S → Prop)

#check (AlgebraicGeometry.isomorphismPresheaf.isAlgebraicSpace_iff :
  ∀ {S : Scheme.{u}}
    (X : GroupoidsOver S),
    isomorphismPresheaf.isAlgebraicSpace X ↔
      ∀ ⦃U : Over S⦄ (x y : X.p.Fiber U),
        isomorphismPresheaf.isAlgebraicSpaceAt x y)

/- Lemma 94.10.11. The diagonal criterion and the algebraic-space Isom condition. -/
@[stacks 045G]
#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff_isom :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      isomorphismPresheaf.isAlgebraicSpace X)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ ⦃U : Over S⦄ (x : X.p.Fiber U),
        relativelyRepresentableByAlgebraicSpaces (YonedaSlice.representative x))

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.yoneda_of_diagonal :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) →
    ∀ {U : Over S} (x : X.p.Fiber U),
    relativelyRepresentableByAlgebraicSpaces (YonedaSlice.representative x))

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_of_yoneda :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S},
    (∀ ⦃U : Over S⦄ (x : X.p.Fiber U),
      relativelyRepresentableByAlgebraicSpaces (YonedaSlice.representative x)) →
    relativelyRepresentableByAlgebraicSpaces
      (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X))

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff_slice :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ ⦃U : Over S⦄ (G : GroupoidsOver.slice U ⟶ X),
        relativelyRepresentableByAlgebraicSpaces G)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff_slicePair :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ ⦃T₁ T₂ : Over S⦄ (x₁ : X.p.Fiber T₁) (x₂ : X.p.Fiber T₂),
        IsRepresentableByAlgebraicSpace
          (TwoFibreProduct.apex.{u + 1, u, u + 1, u}
            (YonedaSlice.representative x₁) (YonedaSlice.representative x₂)))

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofRepresentable :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {U : GroupoidsOver S} (f : U ⟶ X),
        FiberedCategoryOver.Groupoids.IsRepresentable U →
          relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofRepresentablePair :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {T₁ T₂ : GroupoidsOver S} (x₁ : T₁ ⟶ X) (x₂ : T₂ ⟶ X),
        FiberedCategoryOver.Groupoids.IsRepresentable T₁ →
          FiberedCategoryOver.Groupoids.IsRepresentable T₂ →
            IsRepresentableByAlgebraicSpace
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} x₁ x₂))

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofAlgebraicSpace :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {U : GroupoidsOver S} (f : U ⟶ X),
        IsRepresentableByAlgebraicSpace U →
          relativelyRepresentableByAlgebraicSpaces f)

#check (AlgebraicGeometry.relativelyRepresentableByAlgebraicSpaces.diagonal_iff_ofAlgebraicSpacePair :
  ∀ {S : Scheme.{u}} (X : GroupoidsOver S),
    relativelyRepresentableByAlgebraicSpaces
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} X) ↔
      ∀ {T₁ T₂ : GroupoidsOver S} (x₁ : T₁ ⟶ X) (x₂ : T₂ ⟶ X),
        IsRepresentableByAlgebraicSpace T₁ →
          IsRepresentableByAlgebraicSpace T₂ →
            IsRepresentableByAlgebraicSpace
              (TwoFibreProduct.apex.{u + 1, u, u + 1, u} x₁ x₂))
