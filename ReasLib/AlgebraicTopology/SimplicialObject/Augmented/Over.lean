/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Augmentation
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Augmented simplicial objects in a slice category

An augmentation `U ⟶ const X` is equivalently a simplicial object of `C / X`.  This file owns
that topology-independent conversion and its degreewise computation API.
-/

@[expose] public section

noncomputable section

universe v u

namespace CategoryTheory.SimplicialObject.Augmented

open Limits Opposite
open scoped Simplicial

variable {C : Type u} [Category.{v} C]

/-- The degree-zero map of an augmented simplicial object. -/
@[stacks 01GC "degree-zero augmentation map"]
abbrev zeroMap (A : SimplicialObject.Augmented C) :
    A.left.obj (op ⦋0⦌) ⟶ A.right :=
  A.hom.app (op ⦋0⦌)

/-- The two degree-one face maps agree after the degree-zero augmentation. -/
theorem oneMap_condition (A : SimplicialObject.Augmented C) :
    A.left.δ 0 ≫ A.zeroMap = A.left.δ 1 ≫ A.zeroMap := sorry

section Pullbacks

variable [HasPullbacks C]

/-- The degree-one matching map of an augmented simplicial object. -/
@[stacks 01GC "degree-one augmentation matching map"]
noncomputable def oneMap (A : SimplicialObject.Augmented C) :
    A.left.obj (op ⦋1⦌) ⟶ pullback A.zeroMap A.zeroMap :=
  pullback.lift (A.left.δ 0) (A.left.δ 1) A.oneMap_condition

/-- The first projection of the degree-one matching map is the zeroth face map. -/
@[reassoc (attr := simp)] theorem oneMap_fst (A : SimplicialObject.Augmented C) :
    A.oneMap ≫ pullback.fst A.zeroMap A.zeroMap = A.left.δ 0 := sorry

/-- The second projection of the degree-one matching map is the first face map. -/
@[reassoc (attr := simp)] theorem oneMap_snd (A : SimplicialObject.Augmented C) :
    A.oneMap ≫ pullback.snd A.zeroMap A.zeroMap = A.left.δ 1 := sorry

end Pullbacks

/-- The augmentation components commute with every simplicial structure map. -/
theorem toOver_naturality (A : SimplicialObject.Augmented C)
    {Delta Delta' : SimplexCategoryᵒᵖ} (f : Delta ⟶ Delta') :
    A.left.map f ≫ A.hom.app Delta' = A.hom.app Delta := sorry

/-- An augmented simplicial object regarded as a simplicial object in the slice over its
augmentation target. -/
@[stacks 0GM9 "augmented simplicial object in a slice"]
def toOver (A : SimplicialObject.Augmented C) : SimplicialObject (Over A.right) :=
  A.left.toOver A.right (fun Delta ↦ A.hom.app Delta) (fun f ↦ toOver_naturality A f)

/-- The underlying object of `A.toOver` in each degree is the corresponding term of `A`. -/
@[simp] theorem toOver_obj_left (A : SimplicialObject.Augmented C)
    (Delta : SimplexCategoryᵒᵖ) :
    (A.toOver.obj Delta).left = A.left.obj Delta := sorry

/-- The structure arrow of `A.toOver` in each degree is the corresponding augmentation
component. -/
@[simp] theorem toOver_obj_hom (A : SimplicialObject.Augmented C)
    (Delta : SimplexCategoryᵒᵖ) :
    (A.toOver.obj Delta).hom = A.hom.app Delta := sorry

/-- Forgetting a structure morphism of `A.toOver` recovers the simplicial structure map of
`A`. -/
@[simp] theorem toOver_map_left (A : SimplicialObject.Augmented C)
    {Delta Delta' : SimplexCategoryᵒᵖ} (f : Delta ⟶ Delta') :
    (A.toOver.map f).left = A.left.map f := sorry

end CategoryTheory.SimplicialObject.Augmented
