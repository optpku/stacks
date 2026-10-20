/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.Stack.InSetsOver.TwoFibreProduct.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary computations for set-stack two-fibre-product projections

These readouts pass through the proof-bearing set-fibred endpoints and expose the projection
morphisms at the based and total functor layers, where downstream rewriting uses ordinary
equality.
-/

@[expose] public section

noncomputable section

universe u v w vB

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}

namespace StackOver.Sets.TwoFibreProduct

variable {X Y S :
  StackOver.Sets.{u, v, max w (max u (max v vB)), max v vB} J}

/-- The category fibred in sets underlying the stack apex is the neutral selected
two-fibre-product apex. -/
@[stacks 0434 "set-stack two-fibre-product apex set readout"]
theorem apex.toSets (F : X ⟶ S) (G : Y ⟶ S) :
    (apex F G).toSets =
      _root_.CategoryTheory.TwoFibreProduct.apex
        (StackOver.Sets.Hom.toSetsMor F)
        (StackOver.Sets.Hom.toSetsMor G) := sorry

/-- The set-fibred morphism underlying the first stack projection is the neutral first
projection; heterogeneous equality accounts only for proof-bearing endpoints. -/
@[stacks 0434 "set-stack two-fibre-product first projection set readout"]
theorem fst.toSetsMor (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Sets.Hom.toSetsMor (fst F G) ≍
      _root_.CategoryTheory.TwoFibreProduct.fst
        (StackOver.Sets.Hom.toSetsMor F)
        (StackOver.Sets.Hom.toSetsMor G) := sorry

/-- The set-fibred morphism underlying the second stack projection is the neutral second
projection; heterogeneous equality accounts only for proof-bearing endpoints. -/
@[stacks 0434 "set-stack two-fibre-product second projection set readout"]
theorem snd.toSetsMor (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Sets.Hom.toSetsMor (snd F G) ≍
      _root_.CategoryTheory.TwoFibreProduct.snd
        (StackOver.Sets.Hom.toSetsMor F)
        (StackOver.Sets.Hom.toSetsMor G) := sorry

/-- The based functor underlying the first stack projection is the neutral first projection. -/
@[stacks 0434 "set-stack two-fibre-product first projection based readout"]
theorem fst.toBased (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Sets.Hom.toBasedFunctor (fst F G) =
      FiberedCategoryOver.Sets.toBasedFunctor
        (_root_.CategoryTheory.TwoFibreProduct.fst
          (StackOver.Sets.Hom.toSetsMor F)
          (StackOver.Sets.Hom.toSetsMor G)) := sorry

/-- The total functor underlying the first stack projection is the neutral first projection. -/
@[simp, stacks 0434 "set-stack two-fibre-product first projection total readout"]
theorem fst.toTotal (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Sets.Hom.toFunctor (fst F G) =
      FiberedCategoryOver.Sets.toFunctor
        (_root_.CategoryTheory.TwoFibreProduct.fst
          (StackOver.Sets.Hom.toSetsMor F)
          (StackOver.Sets.Hom.toSetsMor G)) := sorry

/-- The based functor underlying the second stack projection is the neutral second projection. -/
@[stacks 0434 "set-stack two-fibre-product second projection based readout"]
theorem snd.toBased (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Sets.Hom.toBasedFunctor (snd F G) =
      FiberedCategoryOver.Sets.toBasedFunctor
        (_root_.CategoryTheory.TwoFibreProduct.snd
          (StackOver.Sets.Hom.toSetsMor F)
          (StackOver.Sets.Hom.toSetsMor G)) := sorry

/-- The total functor underlying the second stack projection is the neutral second projection. -/
@[simp, stacks 0434 "set-stack two-fibre-product second projection total readout"]
theorem snd.toTotal (F : X ⟶ S) (G : Y ⟶ S) :
    StackOver.Sets.Hom.toFunctor (snd F G) =
      FiberedCategoryOver.Sets.toFunctor
        (_root_.CategoryTheory.TwoFibreProduct.snd
          (StackOver.Sets.Hom.toSetsMor F)
          (StackOver.Sets.Hom.toSetsMor G)) := sorry

end StackOver.Sets.TwoFibreProduct

end CategoryTheory
