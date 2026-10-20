/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul braiding on graded modules

This file constructs the signed braiding on `ℤ`-graded modules over a commutative ring.  The
resulting symmetric-category structure is an explicit value rather than a global instance:
graded modules also carry the unsigned pointwise symmetric structure, so instance inference
cannot choose coherently between the two braidings.
-/

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.GradedObject.Monoidal

open CategoryTheory MonoidalCategory

variable {R : Type u} [CommRing R]

/-- The signed swap on the `(p, q)` homogeneous summand of a graded tensor product. -/
def koszulBraidingComponent (V W : GradedObject ℤ (ModuleCat R)) (p q : ℤ) :
    V p ⊗ W q ⟶ W q ⊗ V p :=
  ((p * q).negOnePow : R) • (β_ (V p) (W q)).hom

/-- The morphism on graded tensor products descended from all signed homogeneous swaps. -/
def koszulBraidingHom (V W : GradedObject ℤ (ModuleCat R)) : V ⊗ W ⟶ W ⊗ V :=
  fun n ↦ tensorObjDesc fun p q h ↦
    koszulBraidingComponent V W p q ≫
      ιTensorObj W V q p n (Eq.trans (add_comm q p) h)

/-- The Koszul-signed braiding isomorphism on graded modules. -/
noncomputable def koszulBraiding (V W : GradedObject ℤ (ModuleCat R)) : V ⊗ W ≅ W ⊗ V where
  hom := koszulBraidingHom V W
  inv := koszulBraidingHom W V
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The explicit symmetric-category structure whose commutativity constraint is the Koszul
braiding.  It is intentionally not registered as an instance because the unsigned braiding is a
second coherent choice on the same category. -/
@[stacks 0FFX, implicit_reducible]
noncomputable def koszulSymmetricCategory :
    SymmetricCategory (GradedObject ℤ (ModuleCat R)) where
  toBraidedCategory :=
    { braiding := koszulBraiding
      braiding_naturality_left := sorry
      braiding_naturality_right := sorry
      hexagon_forward := sorry
      hexagon_reverse := sorry }
  symmetry := sorry

/-- Restricting the Koszul braiding to a homogeneous summand gives the signed ordinary swap. -/
@[reassoc]
theorem ι_koszulBraiding_hom (V W : GradedObject ℤ (ModuleCat R))
    (p q n : ℤ) (h : p + q = n) :
    ιTensorObj V W p q n h ≫ (koszulBraiding V W).hom n =
      koszulBraidingComponent V W p q ≫
        ιTensorObj W V q p n (Eq.trans (add_comm q p) h) := sorry

end CategoryTheory.GradedObject.Monoidal
