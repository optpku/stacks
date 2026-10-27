/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RegularImmersion.Permanence
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.44.9 (1): For immersions of algebraic spaces with locally
of finite presentation second map and locally split conormal transitivity,
quasi-regularity of the composite descends to the first map. -/
@[stacks 09S1] #check (AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion.of_comp_of_split_conormal :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
      [hi : AlgebraicGeometry.AlgebraicSpace.IsImmersion i]
      [hj : AlgebraicGeometry.AlgebraicSpace.IsImmersion j]
      [hj_lfp : AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation j]
      (hconormal : AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
      [hcomp : AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion (i ≫ j)],
      AlgebraicGeometry.AlgebraicSpace.IsQuasiRegularImmersion i)

/- Lemma 76.44.9 (2): For immersions of algebraic spaces with locally
of finite presentation second map and locally split conormal transitivity,
`H₁`-regularity of the composite descends to the first map. -/
@[stacks 09S1] #check (AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion.of_comp_of_split_conormal :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
      [hi : AlgebraicGeometry.AlgebraicSpace.IsImmersion i]
      [hj : AlgebraicGeometry.AlgebraicSpace.IsImmersion j]
      [hj_lfp : AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation j]
      (hconormal : AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
      [hcomp : AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion (i ≫ j)],
      AlgebraicGeometry.AlgebraicSpace.IsH1RegularImmersion i)

/- Lemma 76.44.9 (3): For immersions of algebraic spaces with the second map
and composite Koszul-regular and locally split conormal transitivity,
Koszul-regularity descends to the first map. -/
@[stacks 09S1] #check (AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion.of_comp_of_split_conormal :
    ∀ {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
      [hi : AlgebraicGeometry.AlgebraicSpace.IsImmersion i]
      [hj_lfp : AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation j]
      [hj : AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion j]
      (hconormal : AlgebraicGeometry.AlgebraicSpace.Hom.Conormal.Transitivity.IsShortExactLocallySplit i j)
      [hcomp : AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion (i ≫ j)],
      AlgebraicGeometry.AlgebraicSpace.IsKoszulRegularImmersion i)
