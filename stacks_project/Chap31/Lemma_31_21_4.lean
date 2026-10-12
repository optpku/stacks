/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.BaseChange
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 31.21.4 (1): Flat base change of a regular immersion is a regular immersion. -/
@[stacks 067P] #check
  (AlgebraicGeometry.isRegularImmersion_pullback_snd :
    ∀ {X X' Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X)
      [AlgebraicGeometry.IsRegularImmersion i] [AlgebraicGeometry.Flat f],
      AlgebraicGeometry.IsRegularImmersion (CategoryTheory.Limits.pullback.snd i f))

/- Lemma 31.21.4 (2): Flat base change of a Koszul-regular immersion is a
Koszul-regular immersion. -/
@[stacks 067P] #check
  (AlgebraicGeometry.isKoszulRegularImmersion_pullback_snd :
    ∀ {X X' Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X)
      [AlgebraicGeometry.IsKoszulRegularImmersion i] [AlgebraicGeometry.Flat f],
      AlgebraicGeometry.IsKoszulRegularImmersion (CategoryTheory.Limits.pullback.snd i f))

/- Lemma 31.21.4 (3): Flat base change of an `H_1`-regular immersion is an
`H_1`-regular immersion. -/
@[stacks 067P] #check
  (AlgebraicGeometry.isH1RegularImmersion_pullback_snd :
    ∀ {X X' Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X)
      [AlgebraicGeometry.IsH1RegularImmersion i] [AlgebraicGeometry.Flat f],
      AlgebraicGeometry.IsH1RegularImmersion (CategoryTheory.Limits.pullback.snd i f))

/- Lemma 31.21.4 (4): Flat base change of a quasi-regular immersion is a
quasi-regular immersion. -/
@[stacks 067P] #check
  (AlgebraicGeometry.isQuasiRegularImmersion_pullback_snd :
    ∀ {X X' Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) (f : X' ⟶ X)
      [AlgebraicGeometry.IsQuasiRegularImmersion i] [AlgebraicGeometry.Flat f],
      AlgebraicGeometry.IsQuasiRegularImmersion (CategoryTheory.Limits.pullback.snd i f))
