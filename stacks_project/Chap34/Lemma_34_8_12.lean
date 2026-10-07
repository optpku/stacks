module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
import StacksCheckRecall

universe u

/- Lemma 34.8.12: for a scheme `S`, the finite ph covering families on affine schemes over
`S` form a pretopology on `S.AffineOver`. -/
@[stacks 0DBM] #check
  (AlgebraicGeometry.Scheme.bigAffinePhPretopology.{u} :
    (S : AlgebraicGeometry.Scheme.{u}) → CategoryTheory.Pretopology S.AffineOver)
