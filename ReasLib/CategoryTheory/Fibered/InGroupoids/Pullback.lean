/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.CategoryTheory.Fibered.InGroupoids
public import ReasLib.CategoryTheory.Fibered.StronglyCartesian.Pullback.Stability
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pullback existence in categories fibred in groupoids

Mathlib owns the chosen apex, second projection, and their projection/lift facts, while
`Functor.IsStronglyCartesian.Pullback` owns the genuinely new first projection and total-square
criterion. This leaf retains only the groupoid-fibration specialization of pullback existence.
-/

@[expose] public section

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.IsFibered.InGroupoids.Pullback

variable {C : Type u₁} [Category.{v₁} C]
variable {E : Type u₂} [Category.{v₂} E]

/-- Lemma 4.35.15 (Stacks 06N6) (1): if the images of two morphisms under a groupoid-fibred
functor have a pullback, then the original morphisms have a pullback. -/
@[stacks 06N6 "(1) pullback existence for groupoid-fibred functors"]
theorem hasPullback
    (p : E ⥤ C) [Functor.IsFibered.InGroupoids p]
    {x y z : E} (φ : x ⟶ y) (ψ : z ⟶ y)
    [HasPullback (p.map φ) (p.map ψ)] :
    HasPullback φ ψ := sorry

/-- A groupoid-fibred projection preserves pullbacks.  This packages the fact that every total
morphism is strongly cartesian and that strongly-cartesian pullback squares remain pullbacks in
the base. -/
@[stacks 06N6 "groupoid-fibred projections preserve pullbacks"]
instance preservesWalkingCospan
    (p : E ⥤ C) [Functor.IsFibered.InGroupoids p] :
    PreservesLimitsOfShape WalkingCospan p := sorry

end CategoryTheory.Functor.IsFibered.InGroupoids.Pullback
