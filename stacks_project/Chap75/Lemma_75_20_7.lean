/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_20_7_BaseChange
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 75.20.7 (1): in a Tor-independent cartesian square of algebraic spaces,
derived pullback preserves a fixed Tor-amplitude interval relative to the base. -/
@[stacks 0DKD] #check
  (@AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.hasTorAmplitudeInOver :
    {S : AlgebraicGeometry.Scheme.{u}} →
      {X' X Y' Y : AlgebraicGeometry.AlgebraicSpace S} →
      (g' : X' ⟶ X) → (f' : X' ⟶ Y') → (f : X ⟶ Y) → (g : Y' ⟶ Y) →
      (sq : CategoryTheory.IsPullback g' f' f g) →
      (hTor : AlgebraicGeometry.AlgebraicSpace.TorIndependentOver
        (CategoryTheory.Over.mk f) (CategoryTheory.Over.mk g)) →
      (E : AlgebraicGeometry.AlgebraicSpace.ModuleDerived X) → (a b : ℤ) →
      (hE : AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeInOver f E a b) →
      AlgebraicGeometry.AlgebraicSpace.ModuleDerived.HasTorAmplitudeInOver f'
        ((AlgebraicGeometry.AlgebraicSpace.modulePullbackDerived g').obj E) a b)

/- Lemma 75.20.7 (2): in a Tor-independent cartesian square of algebraic spaces,
a module flat over the base computes derived pullback at its degree-zero complex. -/
@[stacks 0DKD] #check
  (@AlgebraicGeometry.AlgebraicSpace.TorIndependentBaseChange.computesAtSingle :
    {S : AlgebraicGeometry.Scheme.{u}} →
      {X' X Y' Y : AlgebraicGeometry.AlgebraicSpace S} →
      (g' : X' ⟶ X) → (f' : X' ⟶ Y') → (f : X ⟶ Y) → (g : Y' ⟶ Y) →
      (sq : CategoryTheory.IsPullback g' f' f g) →
      (hTor : AlgebraicGeometry.AlgebraicSpace.TorIndependentOver
        (CategoryTheory.Over.mk f) (CategoryTheory.Over.mk g)) →
      (𝒢 : X.Modules) →
      (h𝒢 : AlgebraicGeometry.AlgebraicSpace.Modules.flatOver 𝒢 f) →
      CategoryTheory.Functor.LeftDerived.ComputesAt
        (AlgebraicGeometry.AlgebraicSpace.modulePullbackToDerived g')
        (AlgebraicGeometry.AlgebraicSpace.ModuleQis X)
        ((HomotopyCategory.singleFunctor X.Modules 0).obj 𝒢))
