/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Torsion.Regular

open AlgebraicGeometry

universe u

/- Lemma 31.11.11: let `X` be an integral regular scheme of topological Krull dimension at most
one, and let `ℱ` be a coherent `𝒪_X`-module. Then `ℱ` is torsion free if and only if it is finite
locally free. -/
@[stacks 0CC4] #check
  (AlgebraicGeometry.Scheme.Modules.isTorsionFree_iff_isFiniteLocallyFree_of_topologicalKrullDim_le_one :
    ∀ {X : Scheme.{u}} [IsIntegral X] [Scheme.Regular X]
      (ℱ : X.Modules) [ℱ.IsCoherent],
      topologicalKrullDim X ≤ 1 →
        (AlgebraicGeometry.Scheme.Modules.IsTorsionFree ℱ ↔
          SheafOfModules.IsFiniteLocallyFree ℱ))
