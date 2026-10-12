/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCriterion
import StacksCheckRecall

universe u

/- Lemma 30.3.2: let `X` be a quasi-compact and quasi-separated scheme. If
`H¹(X, I) = 0` for every finite-type quasi-coherent ideal sheaf `I`, then `X` is affine. -/
@[stacks 01XG] #check
  (AlgebraicGeometry.Scheme.isAffine_of_H1_vanishes_for_finiteType_quasiCoherent_idealSheaves :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [CompactSpace X.carrier]
      [QuasiSeparatedSpace X.carrier],
      (∀ I : AlgebraicGeometry.Scheme.IdealSubobject X,
        I.toModule.IsQuasicoherent → I.toModule.IsFiniteType →
          CategoryTheory.Limits.IsZero
            (((SheafOfModules.toSheaf X.ringCatSheaf).obj I.toModule).H' 1
              (⊤ : X.Opens))) →
        AlgebraicGeometry.IsAffine X)
