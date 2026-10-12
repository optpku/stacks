/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Composition

open CategoryTheory

universe u

/- Lemma 31.21.7 (1): the composite of two regular immersions is a regular immersion. -/
@[stacks 067Q]
#check (@AlgebraicGeometry.isRegularImmersion_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.IsRegularImmersion i] [AlgebraicGeometry.IsRegularImmersion j],
    AlgebraicGeometry.IsRegularImmersion (i ≫ j))

/- Lemma 31.21.7 (2): the composite of two Koszul-regular immersions is a
Koszul-regular immersion. -/
@[stacks 067Q]
#check (@AlgebraicGeometry.isKoszulRegularImmersion_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.IsKoszulRegularImmersion i]
    [AlgebraicGeometry.IsKoszulRegularImmersion j],
    AlgebraicGeometry.IsKoszulRegularImmersion (i ≫ j))

/- Lemma 31.21.7 (3): the composite of two `H_1`-regular immersions is an
`H_1`-regular immersion. -/
@[stacks 067Q]
#check (@AlgebraicGeometry.isH1RegularImmersion_comp :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.IsH1RegularImmersion i]
    [AlgebraicGeometry.IsH1RegularImmersion j],
    AlgebraicGeometry.IsH1RegularImmersion (i ≫ j))

/- Lemma 31.21.7 (4): the composite of an `H_1`-regular immersion followed by a
quasi-regular immersion is quasi-regular. -/
@[stacks 067Q]
#check (@AlgebraicGeometry.isQuasiRegularImmersion_comp_of_isH1RegularImmersion :
  ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)
    [AlgebraicGeometry.IsH1RegularImmersion i]
    [AlgebraicGeometry.IsQuasiRegularImmersion j],
    AlgebraicGeometry.IsQuasiRegularImmersion (i ≫ j))
