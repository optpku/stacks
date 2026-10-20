/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.InjectiveResolution
public import ReasLib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Below Injective Derived Comparisons

This leaf specializes the generic K-injective quasi-isomorphism transport API
to bounded-below complexes with injective terms.  The specialization removes
the need for downstream callers to install temporary K-injectivity or derived
category instances.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace InjectivePlus

/-- Precomposition by a quasi-isomorphism is bijective on
homotopy-category maps into a bounded-below complex of injectives. -/
@[stacks 05TF]
theorem precomp_bijective_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜) :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I ↦
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map α ≫ g) := sorry

/-- Precomposition by a quasi-isomorphism is injective on homotopy-category maps into a
bounded-below complex of injectives. -/
@[stacks 05TF "bounded K-injective uniqueness under precomposition"]
theorem precomp_injective_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜) :
    Function.Injective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I ↦
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map α ≫ g) := sorry

/-- Precomposition by a quasi-isomorphism is surjective on homotopy-category maps into a
bounded-below complex of injectives. -/
@[stacks 05TF "bounded K-injective existence under precomposition"]
theorem precomp_surjective_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜) :
    Function.Surjective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I ↦
        (HomotopyCategory.quotient 𝒜 (up ℤ)).map α ≫ g) := sorry

/-- Two lifts into a bounded-below injective complex that agree
after a quasi-isomorphism are homotopic. -/
@[stacks 013S]
theorem homotopic_lifts_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (I : InjectivePlus 𝒜)
    (γ : K ⟶ I) (β₁ β₂ : L ⟶ I)
    (hβ₁ : Nonempty (Homotopy (α ≫ β₁) γ))
    (hβ₂ : Nonempty (Homotopy (α ≫ β₂) γ)) :
    Nonempty (Homotopy β₁ β₂) := sorry

section Derived

variable [HasDerivedCategory.{w} 𝒜]

/-- The homotopy-to-derived comparison is bijective for maps
from any cochain complex to a bounded-below injective complex. -/
@[stacks 05TG]
theorem toDerived_map_bijective
    (L : CochainComplex 𝒜 ℤ) (I : InjectivePlus 𝒜) :
    Function.Bijective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I) → _) := sorry

/-- The homotopy-to-derived comparison is injective for maps into a bounded-below complex of
injectives. -/
@[stacks 05TG "bounded K-injective homotopy-to-derived faithfulness"]
theorem toDerived_map_injective
    (L : CochainComplex 𝒜 ℤ) (I : InjectivePlus 𝒜) :
    Function.Injective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I) → _) := sorry

/-- The homotopy-to-derived comparison is surjective for maps into a bounded-below complex of
injectives. -/
@[stacks 05TG "bounded K-injective homotopy-to-derived fullness"]
theorem toDerived_map_surjective
    (L : CochainComplex 𝒜 ℤ) (I : InjectivePlus 𝒜) :
    Function.Surjective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj L ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj I) → _) := sorry

end Derived

end InjectivePlus

end CochainComplex
