/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Basic
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.OfPresheaf
public import ReasLib.CategoryTheory.Fibered.InSets.Bicategory

/-!
# Characteristic functors of morphisms of schemes

The set-valued functor sending `T / S` to a point if `T ⟶ S` factors through a
fixed morphism `S' ⟶ S`, and to empty otherwise, together with the associated
category fibred in groupoids.
-/

@[expose] public section

open CategoryTheory Opposite TypeCat
open AlgebraicGeometry
open FiberedCategoryOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Factorization

/-- The characteristic functor of factoring through `f : S' ⟶ S`: it sends `T` to a
point if `T ⟶ S` factors through `f`, and to empty otherwise. -/
def factorsThroughFunctor {S S' : Scheme.{u}} (f : S' ⟶ S) :
    (Over S)ᵒᵖ ⥤ Type u where
  obj T := ULift.{u} (PLift (Nonempty (T.unop ⟶ Over.mk f)))
  map {X Y} α := TypeCat.ofHom fun x ↦
    ULift.up.{u, 0} (PLift.up (x.down.down.map fun g ↦ α.unop ≫ g))
  map_id _ := by
    ext x
    exact Subsingleton.elim _ _
  map_comp _ _ := by
    ext x
    exact Subsingleton.elim _ _

/-- Evaluating `factorsThroughFunctor f` on `T` recovers the universe-lifted `PLift`
of the existence of a factorization of `T ⟶ S` through `f`. -/
theorem factorsThroughFunctor_obj {S S' : Scheme.{u}} (f : S' ⟶ S)
    (T : (Over S)ᵒᵖ) :
    (factorsThroughFunctor f).obj T =
      ULift.{u} (PLift (Nonempty (T.unop ⟶ Over.mk f))) :=
  sorry

/-- `factorsThroughFunctor f` is nonempty on `T` if and only if `T ⟶ S` factors
through `f`. -/
theorem nonempty_factorsThroughFunctor_iff {S S' : Scheme.{u}} (f : S' ⟶ S)
    (T : (Over S)ᵒᵖ) :
    Nonempty ((factorsThroughFunctor f).obj T) ↔
      Nonempty (T.unop ⟶ Over.mk f) :=
  sorry

/-- The category fibred in groupoids associated to the characteristic functor of
`f : S' ⟶ S`. -/
def toGroupoids {S S' : Scheme.{u}} (f : S' ⟶ S) : GroupoidsOver S :=
  (Sets.toGroupoids (Over S)).obj
    ((Sets.ofPresheaf (Over S)).obj (factorsThroughFunctor f))

/-- The projection of `toGroupoids f` is the opposite category-of-elements
projection of `factorsThroughFunctor f`. -/
theorem toGroupoids_p {S S' : Scheme.{u}} (f : S' ⟶ S) :
    (toGroupoids f).p =
      ((Sets.ofPresheaf (Over S)).obj (factorsThroughFunctor f)).p :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Factorization
