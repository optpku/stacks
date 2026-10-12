/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Limit.Truncation
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 36.3.3: if `E` has quasi-coherent cohomology, then every compatible map from
`E` to a derived limit of its canonical lower-truncation tower `n ↦ τ≥(-n) E` is an
isomorphism. -/
@[stacks 08D3] #check
  (AlgebraicGeometry.Scheme.lowerTruncationComparison_isIso :
    {X : AlgebraicGeometry.Scheme.{u}} →
      (E : DerivedCategory.CohomologyIn
        (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) →
      {K : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace} →
      {c : E.obj ⟶ K} →
      DerivedCategory.Truncation.Lower.Comparison.Exists E.obj c → IsIso c)
