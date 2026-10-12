/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Truncation
public import ReasLib.Algebra.Homology.CochainComplex.Filtration.Truncation.Step

@[expose] public section

/-!
# Truncation filtrations of derived-category representatives

@stack 015X

This leaf packages the canonical truncation filtration on the selected cochain-complex
representative of an object of a derived category. It is independent of a particular abelian
category, boundedness convention, or spectral-sequence application.
-/

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

/-- The canonical truncation filtration on the chosen cochain-complex representative of a
derived-category object. -/
@[stacks 015X "derived representative truncation filtration"]
abbrev truncationFilteredPreimage (K : DerivedCategory 𝒜) : FilteredComplex 𝒜 :=
  (DerivedCategory.Q.objPreimage K).truncationFiltration

namespace TruncationFilteredPreimage

/-- The truncation filtration of a chosen derived-category representative is termwise finite. -/
@[stacks 015X "finite derived representative truncation filtration"]
theorem hasFiniteFiltrations (K : DerivedCategory 𝒜) :
    (truncationFilteredPreimage K).HasFiniteFiltrations := sorry

/-- The stage of the chosen representative's truncation filtration is identified with its
canonical upper truncation. -/
@[stacks 015X "derived representative truncation-filtration stage comparison"]
noncomputable def stageIso
    (K : DerivedCategory 𝒜) (p : ℤ) :
    (truncationFilteredPreimage K).stage p ≅
      (DerivedCategory.Q.objPreimage K).truncLE (-p) :=
  CochainComplex.TruncationFiltration.stageIso (DerivedCategory.Q.objPreimage K) p

/-- The forward map of `stageIso` factors the stage inclusion through the upper truncation
inclusion of the chosen representative. -/
theorem stageIso_hom_comp_inclusion
    (K : DerivedCategory 𝒜) (p : ℤ) :
    (stageIso K p).hom ≫ (DerivedCategory.Q.objPreimage K).ιTruncLE (-p) =
      (truncationFilteredPreimage K).stageInclusion p := sorry

/-- Stage comparison for the truncation filtration of a chosen representative agrees with the
canonical transition between its upper truncations. -/
@[stacks 015X "derived representative truncation-filtration transition"]
theorem stageComparison_hom
    (K : DerivedCategory 𝒜) {p q : ℤ} (hpq : p ≤ q) :
    (truncationFilteredPreimage K).stageComparison hpq ≫ (stageIso K p).hom =
      (stageIso K q).hom ≫
        (DerivedCategory.Q.objPreimage K).truncLEMapOfLE (neg_le_neg hpq) := sorry

/-- A stage-to-truncation map with the canonical composite is the forward map of `stageIso`. -/
theorem hom_eq_of_comp_inclusion
    (K : DerivedCategory 𝒜) (p : ℤ)
    (φ : (truncationFilteredPreimage K).stage p ⟶
      (DerivedCategory.Q.objPreimage K).truncLE (-p))
    (hφ : φ ≫ (DerivedCategory.Q.objPreimage K).ιTruncLE (-p) =
      (truncationFilteredPreimage K).stageInclusion p) :
    φ = (stageIso K p).hom := sorry

end TruncationFilteredPreimage

end CategoryTheory.DerivedCategory
