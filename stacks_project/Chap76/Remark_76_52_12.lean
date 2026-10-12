/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap76.Remark_76_52_12_RelativeExt

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open AlgebraicGeometry.AlgebraicSpace.ModuleDerived

noncomputable section

universe u

/- Remark 76.52.12 (1): under the hypotheses of Lemma 76.52.11, the relative Ext
functor of `K` against `E ⊗ Lf^*(-)` has a pseudo-coherent representative on `Y`. -/
@[stacks 0DKZ]
#check (existsPseudoCoherentRelativeExtRepresentation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [Proper f] [Flat f] [FinitePresentation f]
      [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
      [MonoidalCategory (ModuleDerived Y)] [MonoidalClosed (ModuleDerived Y)]
      (E K : ModuleDerived X) (_ : IsPerfectRelativeTo f E)
      (_ : IsPseudoCoherent X K),
      ∃ L : ModuleDerived Y,
        IsPseudoCoherent Y L ∧ RepresentsRelativeExt f K E L)

/- Remark 76.52.12 (2): any two pseudo-coherent representatives of the relative Ext
functor furnished by Lemma 76.52.11 are isomorphic in `D(𝒪_Y)`. -/
@[stacks 0DKZ]
#check (relativeExtRepresentation_unique :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
      [Proper f] [Flat f] [FinitePresentation f]
      [MonoidalCategory (ModuleDerived X)] [MonoidalClosed (ModuleDerived X)]
      [MonoidalCategory (ModuleDerived Y)] [MonoidalClosed (ModuleDerived Y)]
      (E K : ModuleDerived X) (_ : IsPerfectRelativeTo f E)
      (_ : IsPseudoCoherent X K) (L L' : ModuleDerived Y)
      (_ : IsPseudoCoherent Y L) (_ : IsPseudoCoherent Y L')
      (_ : RepresentsRelativeExt f K E L)
      (_ : RepresentsRelativeExt f K E L'),
      IsIsomorphic L L')
