module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Regular

universe u

/- Lemma 31.12.15: on a regular scheme of topological Krull dimension at most two, a coherent
module is reflexive if and only if it is finite locally free. -/
@[stacks 0B3N] #check
  (@AlgebraicGeometry.Scheme.Modules.isReflexive_iff_isFiniteLocallyFree_of_topologicalKrullDim_le_two :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.Scheme.Regular X]
      (ℱ : X.Modules) [ℱ.IsCoherent],
      topologicalKrullDim X ≤ 2 →
        (AlgebraicGeometry.Scheme.Modules.IsReflexive ℱ ↔
          SheafOfModules.IsFiniteLocallyFree ℱ))
