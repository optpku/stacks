/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap76.Lemma_76_44_3_RegularImmersion
public import stacks_project.Chap76.Lemma_76_44_10_Transitivity

/-!
# Extra permanence for Koszul-regular immersions of locally Noetherian algebraic spaces

For immersions `i : Z ⟶ Y` and `j : Y ⟶ X` of algebraic spaces over a scheme `S`,
with `X` locally Noetherian, Koszul-regularity of the two factors, of the first
factor and the composite, and of the composite together with étale-local splitting
of the canonical conormal transitivity sequence, are equivalent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open Hom.Conormal.Transitivity

/-- Lemma 76.44.10: Let `S` be a scheme. Let `i : Z ⟶ Y` and `j : Y ⟶ X` be
immersions of algebraic spaces over `S`. Assume `X` is locally Noetherian. The
following are equivalent: `i` and `j` are Koszul-regular immersions; `i` and
`i ≫ j` are Koszul-regular immersions; `i ≫ j` is a Koszul-regular immersion
and the canonical conormal transitivity sequence
`0 ⟶ (Modules.pullback i).obj (Hom.conormalSheaf j) ⟶ Hom.conormalSheaf (i ≫ j) ⟶ Hom.conormalSheaf i ⟶ 0`
is exact and étale-locally split. -/
@[stacks 09S2]
theorem isKoszulRegularImmersion_tfae_of_comp_and_conormal
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    List.TFAE
      [ IsKoszulRegularImmersion i ∧ IsKoszulRegularImmersion j
      , IsKoszulRegularImmersion i ∧ IsKoszulRegularImmersion (i ≫ j)
      , IsKoszulRegularImmersion (i ≫ j) ∧
          IsShortExactLocallySplit i j ] :=
  sorry

/-- For immersions of algebraic spaces into a locally Noetherian target, both factors
are Koszul-regular immersions if and only if the first factor and the composite are. -/
theorem isKoszulRegularImmersion_factors_iff_first_and_comp
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    IsKoszulRegularImmersion i ∧ IsKoszulRegularImmersion j ↔
      IsKoszulRegularImmersion i ∧ IsKoszulRegularImmersion (i ≫ j) :=
  sorry

/-- For immersions of algebraic spaces into a locally Noetherian target, both factors
are Koszul-regular immersions if and only if the composite is Koszul-regular and the
canonical conormal transitivity sequence is exact and étale-locally split. -/
theorem isKoszulRegularImmersion_factors_iff_comp_and_splitConormal
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} [IsLocallyNoetherian X]
    (i : Z ⟶ Y) (j : Y ⟶ X) [IsImmersion i] [IsImmersion j] :
    IsKoszulRegularImmersion i ∧ IsKoszulRegularImmersion j ↔
      IsKoszulRegularImmersion (i ≫ j) ∧
        IsShortExactLocallySplit i j :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
