/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.OpenRestriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/- Lemma 56.6.4: for a quasi-compact and quasi-separated scheme and a
quasi-compact open subscheme, restriction induces an equivalence from the
Serre localization by modules supported on the closed complement. -/
@[stacks 0GPH] #check
  (AlgebraicGeometry.Scheme.QCoh.OpenRestriction.quotientFunctorIsEquivalence :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] (U : X.Opens)
      [AlgebraicGeometry.QuasiCompact U.ι],
      (AlgebraicGeometry.Scheme.QCoh.OpenRestriction.quotientFunctor U).IsEquivalence)

end AlgebraicGeometry.Scheme.QCoh
