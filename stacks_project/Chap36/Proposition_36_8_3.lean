/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison.Noetherian

@[expose] public section

open CategoryTheory

universe u

/- Proposition 36.8.3: for a Noetherian scheme, the canonical comparison functor is an
equivalence with the derived coherator composite as quasi-inverse. -/
@[stacks 09T4] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.comparison_isQuasiInverse_of_isNoetherian :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsNoetherian X],
      (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X).IsQuasiInverse
        ((DerivedCategory.cohomologyIn
            (AlgebraicGeometry.RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).ι ⋙
          (AlgebraicGeometry.Scheme.Modules.ringedSpaceEquivalence X).mapDerivedCategory.inverse ⋙
          AlgebraicGeometry.Scheme.QCoh.Derived.coherator X))

/- The equivalence clause of Proposition 36.8.3. -/
#check
  (AlgebraicGeometry.Scheme.DerivedQCoh.comparisonIsEquivalence :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsNoetherian X],
      (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X).IsEquivalence)
