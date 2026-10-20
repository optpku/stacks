module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.QuasiCompactPullback
import StacksCheckRecall

/-!
# Characterizations of absolutely quasi-separated algebraic spaces

Lemma 66.3.3 records that absolute quasi-separatedness of an algebraic space is equivalent to
quasi-compactness of fibre products of morphisms from quasi-compact schemes, and equivalently
from affine schemes.
-/

universe u

/- Lemma 66.3.3: absolute quasi-separatedness is equivalent to quasi-compactness of fibre
products of morphisms from quasi-compact schemes, equivalently from affine schemes. -/
@[stacks 0AHR] #check
  (AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated.tfae :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (X : AlgebraicGeometry.AlgebraicSpace S),
      List.TFAE [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated X,
        AlgebraicGeometry.AlgebraicSpace.forallQuasiCompactPullback X,
        AlgebraicGeometry.AlgebraicSpace.forallAffineQuasiCompactPullback X])
