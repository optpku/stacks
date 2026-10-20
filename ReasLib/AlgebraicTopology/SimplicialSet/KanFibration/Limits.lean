/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.KanFibration
public import ReasLib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.CategoryTheory.MorphismProperty.LiftingProperty.Sequence
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08NX

# Limits of Kan fibrations

Products and inverse-sequence projections of Kan fibrations are Kan fibrations. The underlying
lifting arguments remain owned by the shape-generic morphism-property API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet.modelCategoryQuillen.fibration

/-- Every projection from the inverse limit of a countable tower of Kan fibrations is a Kan
fibration. -/
@[stacks 08NX "Kan fibrations of inverse-sequence projections"]
instance limitProjection {X : ℕ → SSet.{u}} (f : ∀ n : ℕ, X (n + 1) ⟶ X n)
    {i : ℕ}
    [∀ n : ℕ, Fibration (f n)] :
    Fibration (limit.π (Functor.ofOpSequence f) (Opposite.op i)) := sorry

/-- The product map of a family of Kan fibrations is a Kan fibration. This is the `Fibration`
specialization of the shape-generic product stability theorem. -/
@[stacks 08NY "Kan-fibration specialization of products of right lifting properties"]
instance piMap {ι : Type*} {X Y : ι → SSet.{u}}
    (f : ∀ i, X i ⟶ Y i) [HasProduct X] [HasProduct Y]
    [∀ i, Fibration (f i)] :
    Fibration (Limits.Pi.map f) := sorry

end SSet.modelCategoryQuillen.fibration
