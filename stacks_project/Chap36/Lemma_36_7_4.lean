/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.Qcqs
public import stacks_project.Chap36.Lemma_36_4_1

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.7.4: if derived pushforward along every affine-open inclusion commutes with
the canonical comparisons, then the comparison on a qcqs scheme is an equivalence with the
derived coherator as quasi-inverse. -/
@[stacks 09T6] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.comparison_isQuasiInverse :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X],
      (∀ U : X.affineOpens,
        IsIsomorphic (QCoh.Derived.pushforward U.1.ι ⋙ comparison X)
          (comparison (U : Scheme.{u}) ⋙ pushforwardCohomologyIn U.1.ι)) →
      (comparison X).IsQuasiInverse
        ((DerivedCategory.cohomologyIn
            (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          (Scheme.Modules.ringedSpaceEquivalence X).mapDerivedCategory.inverse ⋙
          QCoh.Derived.coherator X))

end AlgebraicGeometry.Scheme.DerivedQCoh
