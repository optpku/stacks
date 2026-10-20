/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 018H

# Augmentations from zero simplices

Reusable zero-simplex descriptions of morphisms from a simplicial object to a constant
simplicial object.  The canonical API is owned by
`CategoryTheory.SimplicialObject.Augmentation`.
-/

@[expose] public section

open Opposite
open CategoryTheory
open CategoryTheory.SimplicialObject
open SimplexCategory
open scoped Simplicial

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace Augmentation

/-- Bundle a natural transformation to a constant simplicial object as an augmented simplicial
object.  This transparent bridge lets fixed-augmentation APIs reuse the canonical bundled
owner without casts or additional instances. -/
@[stacks 018H "bundling an augmentation"]
abbrev toAugmented {U : SimplicialObject C} {X : C}
    (epsilon : U ⟶ (const C).obj X) : SimplicialObject.Augmented C where
  left := U
  right := X
  hom := epsilon

/-- The simplicial object underlying a bundled augmentation is its source. -/
@[simp, stacks 018H "bundled augmentation source"]
theorem toAugmented.left {U : SimplicialObject C} {X : C}
    (epsilon : U ⟶ (const C).obj X) :
    (toAugmented epsilon).left = U := sorry

/-- The point underlying a bundled augmentation is its constant target. -/
@[simp, stacks 018H "bundled augmentation point"]
theorem toAugmented.right {U : SimplicialObject C} {X : C}
    (epsilon : U ⟶ (const C).obj X) :
    (toAugmented epsilon).right = X := sorry

/-- Bundling an augmentation preserves its natural transformation. -/
@[simp, stacks 018H "bundled augmentation morphism"]
theorem toAugmented.hom {U : SimplicialObject C} {X : C}
    (epsilon : U ⟶ (const C).obj X) :
    (toAugmented epsilon).hom = epsilon := sorry

/-- The degree-zero arrow of a bundled augmentation is its degree-zero component. -/
@[simp, stacks 018H "bundled augmentation degree-zero arrow"]
theorem toAugmented.toArrow {U : SimplicialObject C} {X : C}
    (epsilon : U ⟶ (const C).obj X) :
    Augmented.toArrow.obj (toAugmented epsilon) =
      Arrow.mk (epsilon.app (op ⦋0⦌)) := sorry

/-- The type of degree-zero maps satisfying the two-face compatibility relation for `U` and `X`. -/
@[stacks 018H "compatible augmentation zero-simplex data"]
abbrev Compatible (U : SimplicialObject C) (X : C) :=
  { epsilonZero : U _⦋0⦌ ⟶ X //
      U.δ 0 ≫ epsilonZero = U.δ 1 ≫ epsilonZero }

/-- The degree-zero component of an augmentation equalizes the two face maps out of degree one. -/
@[stacks 018H "augmentation face compatibility"]
theorem face_eq
    {U : SimplicialObject C} {X : C} (alpha : U ⟶ (const C).obj X) :
    U.δ 0 ≫ alpha.app (op ⦋0⦌) = U.δ 1 ≫ alpha.app (op ⦋0⦌) := sorry

/-- A compatible zero-simplex has equal composites along any two maps out of the zero simplex. -/
@[stacks 018H "augmentation all-maps compatibility"]
theorem map_eq
    {U : SimplicialObject C} {X : C}
    (epsilonZero : U _⦋0⦌ ⟶ X)
    (h_epsilonZero : U.δ 0 ≫ epsilonZero = U.δ 1 ≫ epsilonZero)
    (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i) :
    U.map g₁.op ≫ epsilonZero = U.map g₂.op ≫ epsilonZero := sorry

/-- The all-maps compatibility theorem packaged for a `Compatible` zero-simplex. -/
@[stacks 018H "compatible zero-simplex all-maps equality"]
theorem Compatible.map_eq
    {U : SimplicialObject C} {X : C} (e : Compatible U X)
    (i : SimplexCategory) (g₁ g₂ : ⦋0⦌ ⟶ i) :
    U.map g₁.op ≫ e.1 = U.map g₂.op ≫ e.1 := sorry

namespace Compatible

/-- Pulling a compatible zero-simplex back along a simplicial morphism preserves the
two-face compatibility relation. -/
@[stacks 018H "compatible augmentation data under precomposition"]
theorem precomp.condition
    {U V : SimplicialObject C} {X : C} (e : Compatible U X) (f : V ⟶ U) :
    V.δ 0 ≫ (f.app (op ⦋0⦌) ≫ e.1) =
      V.δ 1 ≫ (f.app (op ⦋0⦌) ≫ e.1) := sorry

/-- Pull compatible augmentation data back along a morphism of simplicial objects. -/
@[stacks 018H "compatible augmentation data precomposition"]
def precomp
    {U V : SimplicialObject C} {X : C} (e : Compatible U X) (f : V ⟶ U) :
    Compatible V X :=
  ⟨f.app (op ⦋0⦌) ≫ e.1, precomp.condition e f⟩

/-- The value of pulled-back compatible augmentation data is precomposition at degree zero. -/
@[simp, stacks 018H "compatible augmentation precomposition value"]
theorem precomp.val
    {U V : SimplicialObject C} {X : C} (e : Compatible U X) (f : V ⟶ U) :
    (e.precomp f).1 = f.app (op ⦋0⦌) ≫ e.1 := sorry

/-- Postcomposing a compatible zero-simplex preserves the two-face compatibility relation. -/
@[stacks 018H "compatible augmentation data under postcomposition"]
theorem postcomp.condition
    {U : SimplicialObject C} {X Y : C} (e : Compatible U X) (g : X ⟶ Y) :
    U.δ 0 ≫ (e.1 ≫ g) = U.δ 1 ≫ (e.1 ≫ g) := sorry

/-- Postcompose compatible augmentation data by a morphism of target objects. -/
@[stacks 018H "compatible augmentation data postcomposition"]
def postcomp
    {U : SimplicialObject C} {X Y : C} (e : Compatible U X) (g : X ⟶ Y) :
    Compatible U Y :=
  ⟨e.1 ≫ g, postcomp.condition e g⟩

/-- The value of postcomposed compatible augmentation data is the corresponding composite. -/
@[simp, stacks 018H "compatible augmentation postcomposition value"]
theorem postcomp.val
    {U : SimplicialObject C} {X Y : C} (e : Compatible U X) (g : X ⟶ Y) :
    (e.postcomp g).1 = e.1 ≫ g := sorry

end Compatible

/-- Extract the compatible zero-simplex from an augmentation to a constant simplicial object. -/
@[stacks 018H "augmentation zero-simplex classification data"]
def zeroSimplex
    {U : SimplicialObject C} {X : C} (alpha : U ⟶ (const C).obj X) :
    Compatible U X :=
  ⟨alpha.app (op ⦋0⦌), face_eq alpha⟩

/-- Construct an augmentation from a compatible zero-simplex. -/
@[stacks 018H "augmentation from a zero-simplex"]
def ofZeroSimplex
    {U : SimplicialObject C} {X : C} (e : Compatible U X) :
    U ⟶ (const C).obj X :=
  (U.augment X e.1 (Compatible.map_eq e)).hom

/-- Reconstructing an augmentation from its zero-simplex recovers the original augmentation. -/
@[stacks 018H "augmentation reconstruction inverse law"]
theorem of_zeroSimplex
    {U : SimplicialObject C} {X : C} (alpha : U ⟶ (const C).obj X) :
    ofZeroSimplex (zeroSimplex alpha) = alpha := sorry

/-- Extracting a zero-simplex from its reconstructed augmentation recovers the original datum. -/
@[stacks 018H "augmentation extraction inverse law"]
theorem zeroSimplex_of
    {U : SimplicialObject C} {X : C} (e : Compatible U X) :
    zeroSimplex (ofZeroSimplex e) = e := sorry

/-- Augmentations to a constant object are equivalent to compatible zero-simplices. -/
@[stacks 018H "augmentation zero-simplex equivalence"]
def equiv
    (U : SimplicialObject C) (X : C) :
    (U ⟶ (const C).obj X) ≃ Compatible U X where
  toFun := zeroSimplex
  invFun := ofZeroSimplex
  left_inv := of_zeroSimplex
  right_inv := zeroSimplex_of

/-- Augmentations to a constant simplicial object are determined by their degree-zero
components. -/
@[ext, stacks 018H "augmentation extensionality at degree zero"]
theorem hom_ext
    {U : SimplicialObject C} {X : C}
    {alpha beta : U ⟶ (const C).obj X}
    (h : alpha.app (op ⦋0⦌) = beta.app (op ⦋0⦌)) :
    alpha = beta := sorry

/-- The forward map of `equiv` is the degree-zero component with its compatibility proof. -/
@[simp, stacks 018H "augmentation equivalence forward formula"]
theorem equiv.apply
    (U : SimplicialObject C) (X : C) (alpha : U ⟶ (const C).obj X) :
    equiv U X alpha = ⟨alpha.app (op ⦋0⦌), face_eq alpha⟩ := sorry

/-- The augmentation classification equivalence is contravariantly natural in the simplicial
object. -/
@[simp, stacks 018H "augmentation classification under precomposition"]
theorem equiv.precomp
    {U V : SimplicialObject C} {X : C}
    (f : V ⟶ U) (alpha : U ⟶ (const C).obj X) :
    equiv V X (f ≫ alpha) = (equiv U X alpha).precomp f := sorry

/-- The augmentation classification equivalence is covariantly natural in the target object. -/
@[simp, stacks 018H "augmentation classification under postcomposition"]
theorem equiv.postcomp
    {U : SimplicialObject C} {X Y : C}
    (alpha : U ⟶ (const C).obj X) (g : X ⟶ Y) :
    equiv U Y (alpha ≫ (const C).map g) = (equiv U X alpha).postcomp g := sorry

/-- The inverse map of `equiv` is augmentation reconstruction from compatible data. -/
@[simp, stacks 018H "augmentation equivalence inverse formula"]
theorem equiv.symm_apply
    (U : SimplicialObject C) (X : C) (e : Compatible U X) :
    (equiv U X).symm e = ofZeroSimplex e := sorry

/-- The reconstructed augmentation has the prescribed degree-zero component. -/
@[simp, stacks 018H "reconstructed augmentation at degree zero"]
theorem ofZeroSimplex.app_zero {U : SimplicialObject C} {X : C} (e : Compatible U X) :
    (ofZeroSimplex e).app (op ⦋0⦌) = e.1 := sorry

/-- The inverse of `equiv` computes at degree zero to the prescribed zero-simplex. -/
@[simp, stacks 018H "inverse augmentation equivalence at degree zero"]
theorem equiv.symm_apply_app_zero
    (U : SimplicialObject C) (X : C) (e : Compatible U X) :
    ((equiv U X).symm e).app (op ⦋0⦌) = e.1 := sorry

end Augmentation

end CategoryTheory.SimplicialObject
