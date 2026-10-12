/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.EpiMono
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap70.Lemma_70_18_1_BaseChange

/-!
# Étale-local sections of a surjective étale morphism onto a finite scheme

If `π : Z ⟶ U` is a finite morphism of schemes and `W ⟶ Z` is a surjective
étale morphism from an algebraic space, then after a surjective étale base
change of `U` the morphism admits a section.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 97.9.1: Let `π : Z ⟶ U` be a finite morphism of schemes, and let
`W` be an algebraic space over `U` with a surjective étale morphism
`f : W ⟶ ofOver (Over.mk π)`. Then there exists a surjective étale morphism
`g : U' ⟶ U` and a section `σ` of `baseChangeMap g f`. Here
`baseChange g (ofOver (Over.mk π))` is the algebraic-space form of the scheme
pullback `Z ×_U U'`, via `baseChange_ofOver_functorOfPoints`. -/
@[stacks 05XQ]
theorem exists_surjective_etale_baseChange_section
    {U Z : Scheme.{u}} (π : Z ⟶ U) [IsFinite π] {W : AlgebraicSpace U}
    (f : W ⟶ ofOver (Over.mk π)) [Etale f] [Surjective f] :
    ∃ (U' : Scheme.{u}) (g : U' ⟶ U),
      AlgebraicGeometry.Etale g ∧ AlgebraicGeometry.Surjective g ∧
        ∃ (σ : baseChange g (ofOver (Over.mk π)) ⟶ baseChange g W),
          σ ≫ baseChangeMap g f = 𝟙 (baseChange g (ofOver (Over.mk π))) :=
  sorry

/-- Existence of an étale-local section of `baseChangeMap g f` is equivalent to
`IsSplitEpi (baseChangeMap g f)` after a surjective étale base change of `U`. -/
theorem exists_surjective_etale_baseChange_section_iff_isSplitEpi
    {U Z : Scheme.{u}} (π : Z ⟶ U) [IsFinite π] {W : AlgebraicSpace U}
    (f : W ⟶ ofOver (Over.mk π)) [Etale f] [Surjective f] :
    (∃ (U' : Scheme.{u}) (g : U' ⟶ U),
      AlgebraicGeometry.Etale g ∧ AlgebraicGeometry.Surjective g ∧
        ∃ (σ : baseChange g (ofOver (Over.mk π)) ⟶ baseChange g W),
          σ ≫ baseChangeMap g f = 𝟙 (baseChange g (ofOver (Over.mk π)))) ↔
      ∃ (U' : Scheme.{u}) (g : U' ⟶ U),
        AlgebraicGeometry.Etale g ∧ AlgebraicGeometry.Surjective g ∧
          IsSplitEpi (baseChangeMap g f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
