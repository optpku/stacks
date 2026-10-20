/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration
import StacksCheckRecall

/-!
@stack 08NL

# Definition 14.30.1 compatibility facade

The canonical owner is `SSet.modelCategoryQuillen.I.rlp`; ReasLib also exports its equivalent
vertex-surjectivity and positive-dimensional boundary-filling interface.
-/

@[expose] public section

open CategoryTheory Opposite Simplicial
open SSet.modelCategoryQuillen

universe u

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/- The canonical morphism-property owner for trivial Kan fibrations. -/
@[stacks 08NL "Definition 14.30.1"]
#check (I.rlp f : Prop)

/- Definition 14.30.1: a trivial Kan fibration is surjective on vertices and has every
positive-dimensional boundary filler. -/
@[stacks 08NL "Definition 14.30.1 (vertex and boundary characterization)"]
#check (I.rlp.boundary.iff_zero_surjective f :
  I.rlp f ↔
    Function.Surjective (f.app (op ⦋0⦌)) ∧
      ∀ n : ℕ, HasLiftingProperty (∂Δ[n + 1].ι) f)

#check I.rlp.boundary.hasLiftingProperty f
#check I.rlp.zero.surjective f
#check I.rlp.boundary.of_zero_surjective f
#check @MorphismProperty.rlp_of_isIso
