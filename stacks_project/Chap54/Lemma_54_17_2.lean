module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.SurfaceFactorization

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 54.17.2: proper integral regular surfaces over a Noetherian scheme are
birational over the base exactly when they admit a common finite sequence of blowups at
closed points whose composites to the base agree. -/
@[stacks 0C5S] #check
  (AlgebraicGeometry.Scheme.birationalOver_iff_exists_commonPointBlowups :
    ∀ {S X Y : Scheme.{u}} [IsNoetherian S] [X.Over S] [Y.Over S]
      [IsIntegral X] [IsIntegral Y] [Scheme.Regular X] [Scheme.Regular Y]
      [IsProper (X ↘ S)] [IsProper (Y ↘ S)]
      (_ : topologicalKrullDim X = 2) (_ : topologicalKrullDim Y = 2),
      Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
        ∃ (Z : Scheme.{u}) (sX : PointBlowupSequence X Z) (sY : PointBlowupSequence Y Z),
          sX.toSource ≫ (X ↘ S) = sY.toSource ≫ (Y ↘ S))

end AlgebraicGeometry.Scheme
