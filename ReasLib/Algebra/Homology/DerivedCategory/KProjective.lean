/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Quasi-Isomorphism Transport from K-Projective Complexes

This is the projective dual of `DerivedCategory.KInjective`.  It records
transport and uniqueness of homotopy-category maps out of arbitrary
K-projective cochain complexes, before bounded-above termwise-projective
specialization.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v u

namespace CochainComplex.IsKProjective

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 0648: postcomposition by a quasi-isomorphism is bijective on
homotopy-category maps out of any K-projective cochain complex. -/
@[stacks 0648]
theorem postcomp_bijective_of_quasiIso
    {K L P : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [P.IsKProjective] :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map α) := sorry

/-- Postcomposition by a quasi-isomorphism is injective on homotopy-category maps out of a
K-projective complex. -/
@[stacks 0648 "K-projective uniqueness under postcomposition"]
theorem postcomp_injective_of_quasiIso
    {K L P : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [P.IsKProjective] :
    Function.Injective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map α) := sorry

/-- Postcomposition by a quasi-isomorphism is surjective on homotopy-category maps out of a
K-projective complex. -/
@[stacks 0648 "K-projective existence under postcomposition"]
theorem postcomp_surjective_of_quasiIso
    {K L P : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [P.IsKProjective] :
    Function.Surjective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map α) := sorry

/-- Stacks 064A: two homotopy lifts from a K-projective source through a
quasi-isomorphism are homotopic when they agree after postcomposition. -/
@[stacks 064A]
theorem homotopic_lifts_of_quasiIso
    {K L P : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [P.IsKProjective]
    (γ : P ⟶ L) (β₁ β₂ : P ⟶ K)
    (hβ₁ : Nonempty (Homotopy (β₁ ≫ α) γ))
    (hβ₂ : Nonempty (Homotopy (β₂ ≫ α) γ)) :
    Nonempty (Homotopy β₁ β₂) := sorry

/-- A map out of a K-projective complex lifts through a quasi-isomorphism up to homotopy. -/
@[stacks 064A]
theorem exists_homotopy_lift_of_quasiIso
    {K L P : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] [P.IsKProjective]
    (γ : P ⟶ L) :
    ∃ β : P ⟶ K, Nonempty (Homotopy (β ≫ α) γ) := sorry

end CochainComplex.IsKProjective
