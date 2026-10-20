/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Characterizations of universally injective morphisms of algebraic stacks

A morphism of algebraic stacks is universally injective if and only if its
relative 2-diagonal is surjective, or equivalently if it lifts 2-arrows between
algebraically closed field-valued points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)

/-- A morphism `f : X ⟶ Y` of groupoid fibrations lifts 2-arrows between
`Spec(k)`-points for algebraically closed fields: for every algebraically
closed field `k`, structure map `σ : Spec (.of k) ⟶ S`, and 1-morphisms
`x1, x2` from the slice of `σ` to `X`, every 2-iso `x1 ≫ f ≅ x2 ≫ f` is
`whiskerRightIso α f` for some 2-iso `α : x1 ≅ x2`. -/
def liftsAlgClosedTwoArrows : Prop :=
  ∀ {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X),
    Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f)

/-- `liftsAlgClosedTwoArrows f` means whiskering 2-isos of algebraically closed
slice maps along `f` is surjective. -/
theorem liftsAlgClosedTwoArrows_iff : liftsAlgClosedTwoArrows f ↔
    ∀ (k : Type u) [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
      (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X),
      Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f) :=
  sorry

namespace liftsAlgClosedTwoArrows

/-- Surjectivity of `whiskerRightIso (·) f` on algebraically closed slice maps
witnesses `liftsAlgClosedTwoArrows f`. -/
theorem of
    (h : ∀ {k : Type u} [Field k] [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
      (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X),
      Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f)) :
    liftsAlgClosedTwoArrows f :=
  sorry

/-- Under `liftsAlgClosedTwoArrows f`, whiskering 2-isos of algebraically closed
slice maps along `f` is surjective. -/
theorem spec (h : liftsAlgClosedTwoArrows f) {k : Type u} [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X) :
    Function.Surjective (fun α : x1 ≅ x2 ↦ whiskerRightIso α f) :=
  sorry

/-- Under `liftsAlgClosedTwoArrows f`, every 2-iso `β : x1 ≫ f ≅ x2 ≫ f` of
algebraically closed slice maps is `whiskerRightIso α f` for some
`α : x1 ≅ x2`. -/
theorem exists_whisker (h : liftsAlgClosedTwoArrows f) {k : Type u} [Field k]
    [IsAlgClosed k] (σ : Spec (.of k) ⟶ S)
    (x1 x2 : GroupoidsOver.slice (Over.mk σ) ⟶ X)
    (β : x1 ≫ f ≅ x2 ≫ f) :
    ∃ α : x1 ≅ x2, β = whiskerRightIso α f :=
  sorry

end liftsAlgClosedTwoArrows

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.AlgebraicStack

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- For a morphism `f : X ⟶ Y` of algebraic stacks, the
following are equivalent: `UniversallyInjective f`; the relative 2-diagonal
`Hom.diagonal f : X ⟶ X ×_Y X` is surjective on points; and
`liftsAlgClosedTwoArrows f`. -/
@[stacks 0CPN]
theorem tfae (f : X ⟶ Y) :
    List.TFAE [UniversallyInjective f,
      Surjective (Hom.diagonal.{u + 1, u, u + 1} f),
      liftsAlgClosedTwoArrows f] :=
  sorry

/-- A morphism of algebraic stacks is universally injective if and only if its
relative 2-diagonal is surjective on points. -/
theorem iff_surjective_diagonal (f : X ⟶ Y) :
    UniversallyInjective f ↔ Surjective (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

/-- A morphism of algebraic stacks is universally injective if and only if it
lifts 2-arrows between algebraically closed field-valued points. -/
theorem iff_liftsAlgClosedTwoArrows (f : X ⟶ Y) :
    UniversallyInjective f ↔ liftsAlgClosedTwoArrows f :=
  sorry

/-- The relative 2-diagonal of a universally injective morphism of algebraic
stacks is surjective on points. -/
instance surjective_diagonal {f : X ⟶ Y} [UniversallyInjective f] :
    Surjective (Hom.diagonal.{u + 1, u, u + 1} f) :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicStack
