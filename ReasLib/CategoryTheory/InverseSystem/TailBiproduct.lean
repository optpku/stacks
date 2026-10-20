/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Limits
public import ReasLib.CategoryTheory.InverseSystem.EventualZero
public import Mathlib.CategoryTheory.Limits.FunctorCategory.BinaryBiproducts
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tail Biproduct Decompositions of Preorder Inverse Systems

An inverse system can eventually split as a fixed summand and a complementary
tail whose transition maps eventually vanish. This leaf separates that concrete
tail presentation from the intrinsic essential-constancy predicate.
-/

open CategoryTheory.Limits

universe uI vI uD vD

namespace CategoryTheory

namespace PreorderInverseSystem

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroMorphisms D] [HasBinaryBiproducts D]

/-- A preorder-indexed inverse system has a tail biproduct decomposition if, after one stage, it
is naturally isomorphic to a constant summand and a complementary system with eventually zero
transition maps. -/
@[stacks 0G39]
def HasTailBiproductDecomposition (F : PreorderInverseSystem I D) : Prop :=
    ∃ i : I, ∃ A : D, ∃ Z : PreorderInverseSystem (Set.Ici i) D,
    ∃ _ : F.tail i ≅ (Functor.const (Set.Ici i)ᵒᵖ).obj A ⊞ Z,
      Transition.EventuallyZero Z

/-- Evaluating a tail biproduct isomorphism on a transition map gives its componentwise
naturality equation. -/
@[reassoc]
theorem tailBiproductIso_hom_naturality {F : PreorderInverseSystem I D} {i : I} {A : D}
    {Z : PreorderInverseSystem (Set.Ici i) D}
    (e : F.tail i ≅ (Functor.const (Set.Ici i)ᵒᵖ).obj A ⊞ Z)
    {j j' : Set.Ici i} (hjj' : j ≤ j') :
    (F.tail i).transitionMap hjj' ≫ (e.app (Opposite.op j)).hom =
      (e.app (Opposite.op j')).hom ≫
        PreorderInverseSystem.transitionMap
          ((Functor.const (Set.Ici i)ᵒᵖ).obj A ⊞ Z) hjj' := sorry

end

end PreorderInverseSystem

namespace IsCofiltered.IsEssentiallyConstant

section

variable {I : Type uI} [Preorder I]
variable {D : Type uD} [Category.{vD} D] [HasZeroObject D] [Preadditive D] [HasShift D ℤ]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Stacks 0G39, Lemma 13.42.1: in a pretriangulated category, a directed preorder-indexed
inverse system is essentially constant exactly when it has a tail biproduct decomposition with
eventually zero complementary transitions. -/
@[stacks 0G39]
theorem iff_hasTailBiproductDecomposition [IsDirectedOrder I]
    (F : PreorderInverseSystem I D) :
    IsCofiltered.IsEssentiallyConstant F ↔ F.HasTailBiproductDecomposition := sorry

end

end IsCofiltered.IsEssentiallyConstant

end CategoryTheory
