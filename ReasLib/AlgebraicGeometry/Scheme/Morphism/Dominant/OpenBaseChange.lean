/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dominance after base change by an open morphism

A dominant morphism remains dominant after base change along a morphism whose underlying map is
open.
-/

@[expose] public section

open CategoryTheory.Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A dominant morphism remains dominant after base change along an open morphism. -/
@[stacks 0H8F]
theorem isDominant_pullbackSnd_of_isDominant_of_isOpenMap
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) [IsDominant f]
    (hg : IsOpenMap g.base) :
    IsDominant (pullback.snd f g) := by
  have hf : Dense (Set.range f) := by
    simpa [DenseRange] using f.denseRange
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_snd]
  exact hf.preimage hg

end AlgebraicGeometry
