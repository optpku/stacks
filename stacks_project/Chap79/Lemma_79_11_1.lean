/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.OverClass
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Definition_67_17_3_SchemeTheoreticDensity
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Descent of morphisms of algebraic spaces along a dense open

A morphism of algebraic spaces over a separated base which factors through a
scheme-theoretically dense open of an fppf-surjective target factors globally
through that surjection.
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 79.11.1: Let `S` be a scheme. Let `B` be an algebraic space over `S`.
Let `f : X ⟶ Y` and `g : X ⟶ Z` be morphisms of algebraic spaces over `B`.
If `Y ↘ B` is separated, `g` is surjective, flat, and locally of finite
presentation, and `ι : V ⟶ Z` is a scheme-theoretically dense open immersion
such that `openInverseImageι g ι ≫ f` factors through `V`, then `f` factors
through `g`. -/
@[stacks 0AEL]
theorem exists_desc_of_isSchemeTheoreticallyDense
    {S : Scheme.{u}} {B X Y Z V : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [OverClass Z B] [Separated (Y ↘ B)]
    {f : X ⟶ Y} {g : X ⟶ Z} [HomIsOver f B] [HomIsOver g B]
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    (ι : V ⟶ Z) [IsOpenImmersion ι] [IsSchemeTheoreticallyDense ι]
    (hV : V ⟶ Y)
    (hV_fac : openInverseImageι g ι ≫ f = openInverseImageTo g ι ≫ hV) :
    ∃ h : Z ⟶ Y, HomIsOver h B ∧ g ≫ h = f := sorry

/-- A factorization of a morphism over `B` through an fppf surjection is itself
a morphism over `B`. -/
theorem exists_desc_homIsOver {S : Scheme.{u}} {B X Y Z : AlgebraicSpace S}
    [OverClass X B] [OverClass Y B] [OverClass Z B]
    {f : X ⟶ Y} {g : X ⟶ Z} [HomIsOver f B] [HomIsOver g B]
    [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {h : Z ⟶ Y} (h_fac : g ≫ h = f) : HomIsOver h B := sorry

/-- Morphisms of algebraic spaces are unique after precomposition with a
surjective flat locally finitely presented morphism. -/
theorem hom_ext_of_comp_eq {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    {g : X ⟶ Z} [Surjective g] [Flat g] [LocallyOfFinitePresentation g]
    {h₁ h₂ : Z ⟶ Y} (h_eq : g ≫ h₁ = g ≫ h₂) : h₁ = h₂ := sorry

end AlgebraicGeometry.AlgebraicSpace
