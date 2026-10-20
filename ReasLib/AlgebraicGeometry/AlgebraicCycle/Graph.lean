/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Graph

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- The integral graph cycle of `f : Y ⟶ X`, obtained by pushing the fundamental cycle of `Y`
along `(f, 𝟙 Y) : Y ⟶ X ×ₖ Y`. -/
noncomputable def graph {k : Type u} [Field k] {X Y : SchemeOverField k}
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    AlgebraicCycle (pullback X.hom Y.hom) ℤ :=
  AlgebraicCycle.map (SchemeOverField.graph f)
    (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ))
    (@AlgebraicCycle.fundamental Y.left
      (LocallyOfFiniteType.isLocallyNoetherian Y.hom) (fun _ ↦ (0 : ℤ)) 0)

/-- The graph cycle is the pushforward of the fundamental cycle along `(f, 𝟙 Y)`. -/
theorem graph_def {k : Type u} [Field k] {X Y : SchemeOverField k}
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    graph f = AlgebraicCycle.map (SchemeOverField.graph f)
      (fun _ ↦ (0 : ℤ)) (fun _ ↦ (0 : ℤ))
      (@AlgebraicCycle.fundamental Y.left
        (LocallyOfFiniteType.isLocallyNoetherian Y.hom) (fun _ ↦ (0 : ℤ)) 0) := sorry

end AlgebraicGeometry.AlgebraicCycle
