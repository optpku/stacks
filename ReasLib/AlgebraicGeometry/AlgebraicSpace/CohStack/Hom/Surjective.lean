/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom

/-!
# Surjective morphisms of groupoid fibrations over schemes

A 1-morphism of categories fibred in groupoids over `Over S` is surjective when every
field-valued object of the target lifts along the underlying total functor up to isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack.Hom

/-- A 1-morphism `f : X ⟶ Y` of categories fibred in groupoids over `Over S` is surjective if
every object of `Y` lying over the spectrum of a field lifts along `Groupoids.toFunctor f` up to
isomorphism in `Y.total`. -/
class Surjective {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) : Prop where
  /-- Every field-valued object of the target lifts along `f` up to isomorphism. -/
  exists_field_valued_lift :
    ∀ {k : Type u} [Field k] (y : Y.total),
      (Y.p.obj y).left = Spec (CommRingCat.of k) →
        ∃ x : X.total, Nonempty (y ≅ (Groupoids.toFunctor f).obj x)

/-- A 1-morphism is surjective if and only if every field-valued object of the target lifts along
its total functor up to isomorphism. -/
theorem surjective_iff {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) :
    Surjective f ↔
      ∀ {k : Type u} [Field k] (y : Y.total),
        (Y.p.obj y).left = Spec (CommRingCat.of k) →
          ∃ x : X.total, Nonempty (y ≅ (Groupoids.toFunctor f).obj x) :=
  sorry

namespace Surjective

/-- The identity 1-morphism of a category fibred in groupoids is surjective. -/
instance id {S : Scheme.{u}}
    {X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)} :
    Surjective (𝟙 X) :=
  sorry

/-- A surjective 1-morphism lifts every field-valued object of the target up to isomorphism. -/
theorem spec {S : Scheme.{u}}
    {X Y : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S)}
    (f : X ⟶ Y) [Surjective f] :
    ∀ {k : Type u} [Field k] (y : Y.total),
      (Y.p.obj y).left = Spec (CommRingCat.of k) →
        ∃ x : X.total, Nonempty (y ≅ (Groupoids.toFunctor f).obj x) :=
  sorry

end Surjective

end AlgebraicGeometry.AlgebraicSpace.CohStack.Hom
