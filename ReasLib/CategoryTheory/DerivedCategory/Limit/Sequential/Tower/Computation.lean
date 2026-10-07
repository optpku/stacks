module

public import ReasLib.CategoryTheory.DerivedCategory.FunctorCategory.DerivedEvaluation.Diagram.Computation
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Stage.Transition
public import ReasLib.CategoryTheory.DerivedCategory.Limit.Sequential.Tower

@[expose] public section

/-!
# Computation Rules for the Derived Stage Tower

This leaf exposes object, transition, and morphism formulas without requiring
downstream users to unfold `Functor.ofOpSequence` or `NatTrans.ofOpSequence`.
-/

open CategoryTheory
open Opposite

noncomputable section

universe wA wSys u v

namespace CategoryTheory.DerivedLimit.Stage

variable {A : Type u} [Category.{v} A] [Abelian A]
variable [HasDerivedCategory.{wA} A]
variable [HasDerivedCategory.{wSys} (SequentialInverseSystem A)]

namespace tower

/-- The `n`th object of the stagewise tower is derived evaluation at `n`. -/
@[simp]
theorem obj (K : DerivedCategory (SequentialInverseSystem A)) (n : ℕ) :
    (tower K).obj (op n) = (derivedEvaluation A n).obj K := sorry

/-- The successor transition of the stagewise tower is the derived successor
comparison. -/
@[simp]
theorem stepMap (K : DerivedCategory (SequentialInverseSystem A)) (n : ℕ) :
    (tower K).stepMap n = (derivedStep A n).app K := sorry

/-- Every transition map of the stagewise tower is the corresponding derived
stage transition. -/
@[simp]
theorem transitionMap (K : DerivedCategory (SequentialInverseSystem A))
    {i j : ℕ} (h : i ≤ j) :
    (tower K).transitionMap h = (derivedTransition A h).app K := sorry

end tower

namespace TowerFunctor

/-- Computation rule for the object assigned by the stagewise tower functor. -/
@[simp]
theorem obj (K : DerivedCategory (SequentialInverseSystem A)) :
    (towerFunctor A).obj K = tower K := sorry

/-- Computation rule for a component of the morphism assigned by the stagewise tower functor. -/
@[simp]
theorem map_app
    {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L) (n : ℕ) :
    ((towerFunctor A).map f).app (op n) =
      (derivedEvaluation A n).map f := sorry

/-- A tower morphism commutes with every derived stage transition. -/
@[reassoc]
theorem map_transition
    {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L)
    {i j : ℕ} (h : i ≤ j) :
    (derivedEvaluation A j).map f ≫ (derivedTransition A h).app L =
      (derivedTransition A h).app K ≫ (derivedEvaluation A i).map f := sorry

/-- A tower morphism commutes with the derived successor transitions. -/
@[reassoc]
theorem map_step
    {K L : DerivedCategory (SequentialInverseSystem A)} (f : K ⟶ L) (n : ℕ) :
    (derivedEvaluation A (n + 1)).map f ≫ (derivedStep A n).app L =
      (derivedStep A n).app K ≫ (derivedEvaluation A n).map f := sorry

end TowerFunctor

end CategoryTheory.DerivedLimit.Stage
