/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_44_3_RegularImmersion
public import stacks_project.Chap76.Lemma_76_44_10_Transitivity

/-!
# Permanence of regular immersions of algebraic spaces along split conormal transitivity

For immersions `i : Z ⟶ Y` and `j : Y ⟶ X` of algebraic spaces over a scheme
`S`, if `j` is locally of finite presentation and the canonical conormal
transitivity sequence is exact and étale-locally split, then quasi-regularity
or `H₁`-regularity of `i ≫ j` descends to `i`, and Koszul-regularity of both
`j` and `i ≫ j` descends to `i`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom.Conormal.Transitivity

namespace IsQuasiRegularImmersion

/-- Lemma 76.44.9 (1): Let `S` be a scheme. Let `i : Z ⟶ Y` and `j : Y ⟶ X` be
immersions of algebraic spaces over `S`. Assume `j` is locally of finite
presentation and that the canonical conormal transitivity sequence
`complex i j` of Lemma 76.5.6, with maps `baseChange i j` and
`projection i j`,
`0 ⟶ (Modules.pullback i).obj (Hom.conormalSheaf j) ⟶ Hom.conormalSheaf (i ≫ j) ⟶ Hom.conormalSheaf i ⟶ 0`,
is exact and locally split. If `i ≫ j` is a quasi-regular immersion, so is
`i`. -/
@[stacks 09S1]
theorem of_comp_of_split_conormal
    {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] [LocallyOfFinitePresentation j]
    (hconormal : IsShortExactLocallySplit i j)
    [IsQuasiRegularImmersion (i ≫ j)] :
    IsQuasiRegularImmersion i :=
  sorry

end IsQuasiRegularImmersion

namespace IsH1RegularImmersion

/-- Lemma 76.44.9 (2): Let `S` be a scheme. Let `i : Z ⟶ Y` and `j : Y ⟶ X` be
immersions of algebraic spaces over `S`. Assume `j` is locally of finite
presentation and that the canonical conormal transitivity sequence
`complex i j` of Lemma 76.5.6, with maps `baseChange i j` and
`projection i j`,
`0 ⟶ (Modules.pullback i).obj (Hom.conormalSheaf j) ⟶ Hom.conormalSheaf (i ≫ j) ⟶ Hom.conormalSheaf i ⟶ 0`,
is exact and locally split. If `i ≫ j` is an `H₁`-regular immersion, so is
`i`. -/
@[stacks 09S1]
theorem of_comp_of_split_conormal
    {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [IsImmersion j] [LocallyOfFinitePresentation j]
    (hconormal : IsShortExactLocallySplit i j)
    [IsH1RegularImmersion (i ≫ j)] :
    IsH1RegularImmersion i :=
  sorry

end IsH1RegularImmersion

namespace IsKoszulRegularImmersion

/-- Lemma 76.44.9 (3): Let `S` be a scheme. Let `i : Z ⟶ Y` and `j : Y ⟶ X` be
immersions of algebraic spaces over `S`. Assume `j` is locally of finite
presentation and that the canonical conormal transitivity sequence
`complex i j` of Lemma 76.5.6, with maps `baseChange i j` and
`projection i j`,
`0 ⟶ (Modules.pullback i).obj (Hom.conormalSheaf j) ⟶ Hom.conormalSheaf (i ≫ j) ⟶ Hom.conormalSheaf i ⟶ 0`,
is exact and locally split. If both `j` and `i ≫ j` are Koszul-regular
immersions, so is `i`. -/
@[stacks 09S1]
theorem of_comp_of_split_conormal
    {S : Scheme.{u}} {Z Y X : AlgebraicSpace S} (i : Z ⟶ Y) (j : Y ⟶ X)
    [IsImmersion i] [LocallyOfFinitePresentation j] [IsKoszulRegularImmersion j]
    (hconormal : IsShortExactLocallySplit i j)
    [IsKoszulRegularImmersion (i ≫ j)] :
    IsKoszulRegularImmersion i :=
  sorry

end IsKoszulRegularImmersion

end AlgebraicGeometry.AlgebraicSpace
