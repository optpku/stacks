/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.CategoryTheory.Homology.SpectralSequence.Abutment
public import stacks_project.Chap94.Definition_94_12_1_MorphismProperty
public import stacks_project.Chap96.Lemma_96_19_10_LocallyOfFinitePresentation
public import stacks_project.Chap100.Lemma_100_11_1_Flat
public import stacks_project.Chap103.Proposition_103_11_7_Pushforward
public import stacks_project.Chap103.Proposition_103_11_7_Cech

/-!
# Relative Čech spectral sequence for quasi-coherent higher direct images

A surjective flat 1-morphism of algebraic stacks that is representable by
algebraic spaces, locally of finite presentation, quasi-compact, and
quasi-separated computes quasi-coherent higher direct images along a
quasi-compact quasi-separated morphism from the relative Čech nerve.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory FiberedCategoryOver.Groupoids
open scoped Bicategory Simplicial

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {U X Y : GroupoidsOver S}

/-- Proposition 103.11.7: Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable
morphisms of algebraic stacks. Assume `f` is representable by algebraic spaces,
surjective, flat, locally of finite presentation, quasi-compact, and
quasi-separated, and `g` is quasi-compact and quasi-separated. If `F` is in
`QCoh(𝒪_𝒳)` then there is a spectral sequence
`E₂^{p, q} = R^q (g ∘ f_p)_{QCoh,*} (f_p^* F) ⇒ R^{p+q} g_{QCoh,*} F`
in `QCoh(𝒪_𝒴)`, where `f_p` is the Čech-nerve projection
`Cech.proj f ⦋p⦌ : 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰 ⟶ 𝒳` on `p+1` factors. The displayed
page is the project's page-1 object
`qcohRelativeCechPushforwardPageOne f g F p q`, and the abutment is
`qCohHigherDirectImage g F`. -/
@[stacks 0785]
theorem exists_qcohRelativeCechPushforwardSpectralSequence
    [AlgebraicStack U] [AlgebraicStack X] [AlgebraicStack Y]
    (f : U ⟶ X) (g : X ⟶ Y) (F : QCoh X)
    [Groupoids.Hom.Surjective f] [Groupoids.Hom.Flat f]
    [Groupoids.Hom.LocallyOfFinitePresentation f]
    [AlgebraicStack.QuasiCompact f] [AlgebraicStack.QuasiSeparated f]
    [AlgebraicStack.QuasiCompact g] [AlgebraicStack.QuasiSeparated g]
    [∀ p, AlgebraicStack (Cech.covering.{u + 1, u, u + 1, u} f ⦋p⦌)]
    [∀ p, AlgebraicStack.QuasiCompact
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)]
    [∀ p, AlgebraicStack.QuasiSeparated
      (Cech.proj.{u + 1, u, u + 1, u} f ⦋p⦌ ≫ g)] :
    ∃ (E : CohomologicalSpectralSequenceNat (QCoh Y) 1)
      (pageOneIso : ∀ p q,
        (E.page 1 le_rfl).X (p, q) ≅
          qcohRelativeCechPushforwardPageOne f g F p q),
      CohomologicalSpectralSequenceNat.ConvergesTo E
        (fun n ↦ qCohHigherDirectImage g F n) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
