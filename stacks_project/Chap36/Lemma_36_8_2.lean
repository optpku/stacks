/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Comparison

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Lemma 36.8.2. For a morphism of Noetherian schemes, right-derived quasicoherent
pushforward commutes, up to natural isomorphism, with the canonical comparisons to derived
modules having quasicoherent cohomology. -/
@[stacks 09T3] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardComparison_isomorphic :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y],
      IsIsomorphic
        (AlgebraicGeometry.Scheme.QCoh.Derived.pushforward f ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.comparison Y)
        (AlgebraicGeometry.Scheme.DerivedQCoh.comparison X ⋙
          AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardCohomologyIn f))
