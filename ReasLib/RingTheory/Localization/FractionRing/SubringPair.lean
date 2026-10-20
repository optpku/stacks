/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Ring.Subring.Intersection
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Pairs of subrings with a common fraction field

This leaf owns the elementary algebra attached to two subrings of a field
which have that field as their common fraction field.  It keeps the
intersection, its component maps, scalar towers, and the tensor comparison
map together, without imposing any dimension or valuation hypotheses.
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace FractionRing

/-- An ordered pair of subrings of a field, each having the ambient field as
its fraction field through its inclusion. -/
@[stacks 09MY "fraction-ring subring pair"]
structure SubringPair (K : Type u) [Field K] where
  /-- The left subring of the ambient field. -/
  left : Subring K
  /-- The right subring of the ambient field. -/
  right : Subring K
  /-- The left inclusion exhibits the ambient field as a fraction field. -/
  leftIsFractionRing : @IsFractionRing left _ K _ left.subtype.toAlgebra
  /-- The right inclusion exhibits the ambient field as a fraction field. -/
  rightIsFractionRing : @IsFractionRing right _ K _ right.subtype.toAlgebra

namespace SubringPair

variable {K : Type u} [Field K]

/-- Construct a fraction-subring pair from two subrings and their canonical
fraction-field structures. -/
@[stacks 09MY "fraction-ring subring pair constructor"]
def ofSubrings (left right : Subring K)
    (leftIsFractionRing : @IsFractionRing left _ K _ left.subtype.toAlgebra)
    (rightIsFractionRing : @IsFractionRing right _ K _ right.subtype.toAlgebra) :
    SubringPair K :=
  { left
    right
    leftIsFractionRing
    rightIsFractionRing }

/-- The intersection of the two subrings, viewed as a subring of the ambient
field. -/
@[reducible, stacks 09MY "fraction-ring subring intersection"]
def intersection (P : SubringPair K) : Subring K :=
  P.left ⊓ P.right

/-- Constructing a pair from two subrings recovers those subrings and their
intersection. -/
@[stacks 09MY "fraction-ring subring pair constructor specification"]
theorem ofSubrings_spec (left right : Subring K)
    (leftIsFractionRing : @IsFractionRing left _ K _ left.subtype.toAlgebra)
    (rightIsFractionRing : @IsFractionRing right _ K _ right.subtype.toAlgebra) :
    (ofSubrings left right leftIsFractionRing rightIsFractionRing).left = left ∧
      (ofSubrings left right leftIsFractionRing rightIsFractionRing).right = right ∧
      (ofSubrings left right leftIsFractionRing rightIsFractionRing).intersection =
        left ⊓ right := sorry

/-- The canonical inclusion from the intersection into the left subring. -/
@[stacks 09MY "intersection inclusion to left subring"]
def toLeft (P : SubringPair K) : P.intersection →+* P.left :=
  Subring.inclusion inf_le_left

/-- The canonical inclusion from the intersection into the right subring. -/
@[stacks 09MY "intersection inclusion to right subring"]
def toRight (P : SubringPair K) : P.intersection →+* P.right :=
  Subring.inclusion inf_le_right

/-- Membership in the intersection is simultaneous membership in the two
component subrings. -/
@[stacks 09MY "fraction-ring intersection membership"]
theorem mem_intersection_iff (P : SubringPair K) {x : K} :
    x ∈ P.intersection ↔ x ∈ P.left ∧ x ∈ P.right := sorry

/-- The component maps from the intersection agree in the ambient field. -/
@[stacks 09MY "fraction-ring intersection component equality"]
theorem subtype_comp_toLeft_eq_subtype_comp_toRight (P : SubringPair K) :
    let leftIncl : P.left →+* K := P.left.subtype
    let rightIncl : P.right →+* K := P.right.subtype
    leftIncl.comp P.toLeft = rightIncl.comp P.toRight := sorry

/-- The left component map preserves the underlying ambient-field element. -/
@[simp]
theorem coe_toLeft (P : SubringPair K) (x : P.intersection) :
    ((P.toLeft x : P.left) : K) = x := sorry

/-- The right component map preserves the underlying ambient-field element. -/
@[simp]
theorem coe_toRight (P : SubringPair K) (x : P.intersection) :
    ((P.toRight x : P.right) : K) = x := sorry

/-- The comparison algebra homomorphism from the tensor product of the two
component subrings to their ambient field. -/
@[stacks 09N0 "fraction-ring tensor comparison map"]
def tensorToAmbient (P : SubringPair K) :
    P.left ⊗[P.intersection] P.right →ₐ[P.intersection] K :=
  Algebra.TensorProduct.productMap
    (IsScalarTower.toAlgHom P.intersection P.left K)
    (IsScalarTower.toAlgHom P.intersection P.right K)

/-- The tensor comparison map sends a pure tensor to the product of its two
ambient-field images. -/
@[stacks 09N0 "fraction-ring tensor comparison on pure tensors"]
theorem tensorToAmbient_apply_tmul (P : SubringPair K) (x : P.left) (y : P.right) :
    P.tensorToAmbient (x ⊗ₜ[P.intersection] y) =
      algebraMap P.left K x * algebraMap P.right K y := sorry

end SubringPair

end FractionRing
