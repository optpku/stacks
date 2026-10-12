/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.Comparison
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 34.6.2: Any smooth covering is a syntomic covering, and a fortiori, any étale or
Zariski covering is a syntomic covering. -/
@[stacks 0226] #check
  (AlgebraicGeometry.Scheme.bigSmoothPrecoverage_le_bigSyntomicPrecoverage :
    AlgebraicGeometry.Scheme.bigSmoothPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage.{u})

#check
  (AlgebraicGeometry.Scheme.etalePrecoverage_le_bigSyntomicPrecoverage :
    AlgebraicGeometry.Scheme.etalePrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage.{u})

#check
  (AlgebraicGeometry.Scheme.zariskiPrecoverage_le_bigSyntomicPrecoverage :
    AlgebraicGeometry.Scheme.zariskiPrecoverage.{u} ≤
      AlgebraicGeometry.Scheme.bigSyntomicPrecoverage.{u})
