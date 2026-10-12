/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplexCategory.DeltaLastIter
public import Mathlib.AlgebraicTopology.SimplicialObject.DeltaZeroIter
public import Mathlib.AlgebraicTopology.SimplicialObject.Op

/-!
# Iterated final faces and degeneracies of simplicial objects

This file is the final-vertex counterpart of Mathlib's `DeltaZeroIter`.  The definitions are
owned at the simplicial-object level, with bridges to the order-reversal functor and the
augmented naturality API needed by contraction constructions.
-/

@[expose] public section

open Simplicial Opposite

namespace CategoryTheory.SimplicialObject

variable {C : Type*} [Category* C] (X : SimplicialObject C)

/-- If `n + i = m`, the morphism `X _⦋m⦌ ⟶ X _⦋n⦌` obtained by iterating the final face
map `i` times. -/
@[stacks 08ND "iterated final face map"]
def δLastIter {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    X _⦋m⦌ ⟶ X _⦋n⦌ :=
  X.map (SimplexCategory.δLastIter i hi).op

/-- If `n + i = m`, the morphism `X _⦋n⦌ ⟶ X _⦋m⦌` obtained by iterating the final
degeneracy map `i` times. -/
@[stacks 08ND "iterated final degeneracy map"]
def σLastIter {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    X _⦋n⦌ ⟶ X _⦋m⦌ :=
  X.map (SimplexCategory.σLastIter i hi).op

/-- Iterating the final face zero times gives the identity. -/
@[simp]
theorem δLastIter_zero (n : ℕ) : X.δLastIter 0 (add_zero n) = 𝟙 _ := sorry

/-- Iterating the final face once gives the final face. -/
@[simp]
theorem δLastIter_one (n : ℕ) :
    X.δLastIter 1 (n := n) rfl = X.δ (Fin.last (n + 1)) := sorry

/-- Iterating the final degeneracy zero times gives the identity. -/
@[simp]
theorem σLastIter_zero (n : ℕ) : X.σLastIter 0 (add_zero n) = 𝟙 _ := sorry

/-- Iterating the final degeneracy once gives the final degeneracy. -/
@[simp]
theorem σLastIter_one (n : ℕ) :
    X.σLastIter 1 (n := n) rfl = X.σ (Fin.last n) := sorry

/-- An iterated final degeneracy followed by the matching iterated final face is the identity. -/
@[reassoc (attr := simp), stacks 08ND "iterated final degeneracy-face identity"]
theorem σLastIter.comp_δLastIter (i : ℕ) {n m : ℕ} (hi : n + i = m) :
    X.σLastIter i hi ≫ X.δLastIter i hi = 𝟙 _ := sorry

/-- An iterated final degeneracy is a monomorphism. -/
instance (i : ℕ) {n m : ℕ} (hi : n + i = m) : Mono (X.σLastIter i hi) := sorry

/-- An iterated final face is an epimorphism. -/
instance (i : ℕ) {n m : ℕ} (hi : n + i = m) : Epi (X.δLastIter i hi) := sorry

/-- Naturality of an iterated final face with respect to a morphism of simplicial objects. -/
@[reassoc]
theorem δLastIter_naturality {Y : SimplicialObject C} (f : X ⟶ Y)
    (i : ℕ) {n m : ℕ} (hi : n + i = m) :
    X.δLastIter i hi ≫ f.app (op ⦋n⦌) =
      f.app (op ⦋m⦌) ≫ Y.δLastIter i hi := sorry

/-- Naturality of an iterated final degeneracy with respect to a morphism of simplicial
objects. -/
@[reassoc]
theorem σLastIter_naturality {Y : SimplicialObject C} (f : X ⟶ Y)
    (i : ℕ) {n m : ℕ} (hi : n + i = m) :
    X.σLastIter i hi ≫ f.app (op ⦋m⦌) =
      f.app (op ⦋n⦌) ≫ Y.σLastIter i hi := sorry

/-- The initial-face iteration on the order reversal of a simplicial object is its final-face
iteration. -/
@[simp, stacks 08ND "order reversal carries initial faces to final faces"]
theorem opFunctor_obj_δ₀Iter {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    (_root_.SimplicialObject.opFunctor.obj X).δ₀Iter i hi = X.δLastIter i hi := sorry

/-- The initial-degeneracy iteration on the order reversal of a simplicial object is its
final-degeneracy iteration. -/
@[simp, stacks 08ND "order reversal carries initial degeneracies to final degeneracies"]
theorem opFunctor_obj_σ₀Iter {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    (_root_.SimplicialObject.opFunctor.obj X).σ₀Iter i hi = X.σLastIter i hi := sorry

/-- The final-face iteration on the order reversal of a simplicial object is its initial-face
iteration. -/
@[simp]
theorem opFunctor_obj_δLastIter {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    (_root_.SimplicialObject.opFunctor.obj X).δLastIter i hi = X.δ₀Iter i hi := sorry

/-- The final-degeneracy iteration on the order reversal of a simplicial object is its
initial-degeneracy iteration. -/
@[simp]
theorem opFunctor_obj_σLastIter {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    (_root_.SimplicialObject.opFunctor.obj X).σLastIter i hi = X.σ₀Iter i hi := sorry

namespace Augmented

variable (Y : Augmented C)

/-- Iterated final faces are compatible with the augmentation. -/
@[reassoc (attr := simp), stacks 08ND "augmentation naturality for iterated final faces"]
theorem δLastIter_hom_app {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    Y.left.δLastIter i hi ≫ Y.hom.app (op ⦋n⦌) = Y.hom.app (op ⦋m⦌) := sorry

/-- Iterated final degeneracies are compatible with the augmentation. -/
@[reassoc (attr := simp), stacks 08ND "augmentation naturality for iterated final degeneracies"]
theorem σLastIter_hom_app {n m : ℕ} (i : ℕ) (hi : n + i = m) :
    Y.left.σLastIter i hi ≫ Y.hom.app (op ⦋m⦌) = Y.hom.app (op ⦋n⦌) := sorry

end Augmented

end CategoryTheory.SimplicialObject
