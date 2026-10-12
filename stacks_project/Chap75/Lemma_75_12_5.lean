/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap75.Lemma_75_12_5_Comparison

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

/- Lemma 75.12.5. For a morphism of Noetherian algebraic spaces, right-derived
quasi-coherent pushforward commutes, up to natural isomorphism, with the canonical
comparisons to derived modules having quasi-coherent cohomology. -/
@[stacks 09TM] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardComparison_isomorphic :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsNoetherian X] [IsNoetherian Y] [QuasiCompact f] [QuasiSeparated f],
      IsIsomorphic
        (QCoh.Derived.pushforward f ⋙ DerivedQCoh.comparison Y)
        (DerivedQCoh.comparison X ⋙ DerivedQCoh.pushforward f))

#check AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforward
#check AlgebraicGeometry.AlgebraicSpace.QCoh.Derived.pushforwardIsRightDerived
