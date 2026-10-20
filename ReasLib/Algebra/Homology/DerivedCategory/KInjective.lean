/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quasi-Isomorphism Transport from K-Injective Complexes

Mathlib supplies the comparison from homotopy-category maps into a K-injective
complex to derived-category maps.  This leaf adds the complementary transport
along a quasi-isomorphism and the resulting uniqueness-up-to-homotopy API.
It is formulated for arbitrary K-injective targets, before any boundedness or
termwise-injectivity specialization.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v u

namespace CochainComplex.IsKInjective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 05TF: precomposition by a quasi-isomorphism is bijective on
homotopy-category maps into any K-injective cochain complex. -/
@[stacks 05TF]
theorem precomp_bijective_of_quasiIso
    {K L I : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [I.IsKInjective] :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I ↦
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map α ≫ g) := sorry

/-- Precomposition by a quasi-isomorphism is injective on homotopy-category maps into a
K-injective complex. -/
@[stacks 05TF "K-injective uniqueness under precomposition"]
theorem precomp_injective_of_quasiIso
    {K L I : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [I.IsKInjective] :
    Function.Injective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I ↦
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map α ≫ g) := sorry

/-- Precomposition by a quasi-isomorphism is surjective on homotopy-category maps into a
K-injective complex. -/
@[stacks 05TF "K-injective existence under precomposition"]
theorem precomp_surjective_of_quasiIso
    {K L I : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [I.IsKInjective] :
    Function.Surjective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I ↦
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map α ≫ g) := sorry

/-- Stacks 013S: two homotopy lifts through a quasi-isomorphism into a
K-injective target are homotopic when they agree after precomposition. -/
@[stacks 013S]
theorem homotopic_lifts_of_quasiIso
    {K L I : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [I.IsKInjective]
    (γ : K ⟶ I) (β₁ β₂ : L ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := sorry

/- A surjective comparison in the homotopy category is often consumed only as an
existence statement.  Keep that specialization next to the bijectivity owner so
callers do not have to unpack the quotient map themselves. -/
/-- A map into a K-injective complex lifts along a quasi-isomorphism up to homotopy. -/
@[stacks 013S]
theorem exists_homotopy_lift_of_quasiIso
    {K L I : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [I.IsKInjective]
    (γ : K ⟶ I) :
    ∃ β : L ⟶ I, Nonempty (Homotopy (α ≫ β) γ) := sorry

end CochainComplex.IsKInjective

