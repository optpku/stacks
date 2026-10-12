/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph.Refinement
import StacksCheckRecall

universe u v

/- Lemma 34.8.5: a Zariski covering is a ph covering. -/
@[stacks 0DBH] #check
  (AlgebraicGeometry.Scheme.OpenCover.phCovering :
    {T : AlgebraicGeometry.Scheme.{u}} → (cover : T.OpenCover.{v}) →
      AlgebraicGeometry.PhCovering
        (fun i : cover.I₀ ↦ cover.X i) (fun i ↦ cover.f i))
