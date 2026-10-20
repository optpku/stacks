/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Skeleton.Tower
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 0193

# Monomorphic maps in a skeleton tower

Monicity of a skeleton counit forces monicity of the following tower transition.  The resulting
objectwise fact is then promoted independently to the natural tower and to every map of an
individual skeleton sequence.  No abelian structure is used in this layer.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Skeleton

variable {C : Type u} [Category.{v} C]

/-- A skeleton successor map is monic whenever the counit at its source stage is monic. -/
@[stacks 0193 "monomorphic skeleton successor map from a monomorphic counit"]
instance succMap_mono (V : SimplicialObject C) (n : ℕ)
    [Truncated.HasSkeletons C n] [Truncated.HasSkeletons C (n + 1)]
    [Mono ((skAdj n).counit.app V)] : Mono (succMap V n) := sorry

namespace Tower

/-- A natural skeleton transition is monic when the source-stage counit is monic. -/
@[stacks 0193 "monomorphic natural skeleton transition from a monomorphic counit"]
instance step_mono (n : ℕ)
    [Truncated.HasSkeletons C n] [Truncated.HasSkeletons C (n + 1)]
    [Mono ((skAdj (C := C) n).counit)] :
    Mono (step (A := C) n) := sorry

end Tower

variable [∀ n, Truncated.HasSkeletons C n]

namespace Tower.diagram

/-- Every map in the functorial skeleton tower is monic when its source-stage counit is monic. -/
@[stacks 0193 "monomorphic map in the functorial skeleton tower"]
instance map_mono {i j : ℕ} (f : i ⟶ j)
    [Mono ((skAdj (C := C) i).counit)] :
    Mono ((Tower.diagram (A := C)).map f) := sorry

end Tower.diagram

namespace sequence

/-- A map in a skeleton sequence is monic whenever the counit at its source stage is monic. -/
@[stacks 0193 "monomorphic skeleton sequence map from its source counit"]
instance map_mono (V : SimplicialObject C) {i j : ℕ} (f : i ⟶ j)
    [Mono ((skAdj i).counit.app V)] : Mono ((sequence V).map f) := sorry

end sequence

end CategoryTheory.SimplicialObject.Skeleton
