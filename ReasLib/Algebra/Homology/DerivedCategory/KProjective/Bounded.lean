/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution
public import ReasLib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Bounded-Above Projective Derived Comparisons

This leaf specializes the generic K-projective quasi-isomorphism transport
API to bounded-above complexes with projective terms.  It gives downstream
users direct theorem applications without temporary K-projectivity or chosen
derived-category instances.
-/

open CategoryTheory
open ComplexShape

noncomputable section

universe w v u

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

namespace ProjectiveMinus

/-- Postcomposition by a quasi-isomorphism is bijective on
homotopy-category maps out of a bounded-above complex of projectives. -/
@[stacks 0648]
theorem postcomp_bijective_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (P : ProjectiveMinus 𝒜) :
    Function.Bijective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map α) := sorry

/-- Postcomposition by a quasi-isomorphism is injective on homotopy-category maps out of a
bounded-above complex of projectives. -/
@[stacks 0648 "bounded K-projective uniqueness under postcomposition"]
theorem postcomp_injective_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (P : ProjectiveMinus 𝒜) :
    Function.Injective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map α) := sorry

/-- Postcomposition by a quasi-isomorphism is surjective on homotopy-category maps out of a
bounded-above complex of projectives. -/
@[stacks 0648 "bounded K-projective existence under postcomposition"]
theorem postcomp_surjective_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (P : ProjectiveMinus 𝒜) :
    Function.Surjective
      (fun g : (HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj K ↦
        g ≫ (HomotopyCategory.quotient 𝒜 (up ℤ)).map α) := sorry

/-- Two lifts from a bounded-above projective source through a
quasi-isomorphism that agree after postcomposition are homotopic. -/
@[stacks 064A]
theorem homotopic_lifts_of_quasiIso
    {K L : CochainComplex 𝒜 ℤ} (α : K ⟶ L) [QuasiIso α] (P : ProjectiveMinus 𝒜)
    (γ : (P : CochainComplex 𝒜 ℤ) ⟶ L)
    (β₁ β₂ : (P : CochainComplex 𝒜 ℤ) ⟶ K)
    (hβ₁ : Nonempty (Homotopy (β₁ ≫ α) γ))
    (hβ₂ : Nonempty (Homotopy (β₂ ≫ α) γ)) :
    Nonempty (Homotopy β₁ β₂) := sorry

section Derived

variable [HasDerivedCategory.{w} 𝒜]

/-- The homotopy-to-derived comparison is bijective for maps
from a bounded-above projective complex to any cochain complex. -/
@[stacks 064B]
theorem toDerived_map_bijective
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) :
    Function.Bijective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) → _) := sorry

/-- The homotopy-to-derived comparison is injective for maps out of a bounded-above complex of
projectives. -/
@[stacks 064B "bounded K-projective homotopy-to-derived faithfulness"]
theorem toDerived_map_injective
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) :
    Function.Injective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) → _) := sorry

/-- The homotopy-to-derived comparison is surjective for maps out of a bounded-above complex of
projectives. -/
@[stacks 064B "bounded K-projective homotopy-to-derived fullness"]
theorem toDerived_map_surjective
    (P : ProjectiveMinus 𝒜) (L : CochainComplex 𝒜 ℤ) :
    Function.Surjective
      (DerivedCategory.Qh.map :
        ((HomotopyCategory.quotient 𝒜 (up ℤ)).obj P ⟶
          (HomotopyCategory.quotient 𝒜 (up ℤ)).obj L) → _) := sorry

end Derived

end ProjectiveMinus

end CochainComplex
