/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.TwoTerm.Composition
import StacksCheckRecall

/-!
# Lemma 15.85.11 (0AJT)

@stack 0AJT
-/

@[expose] public section

open CategoryTheory

universe w v u

/- Lemma 15.85.11 (Stacks `0AJT`): the composite vanishes under the source's `H⁰` and
`H⁻¹` vanishing hypotheses. -/
@[stacks 0AJT "composition vanishing for two-term derived objects"]
#check fun {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]
    {K₁ K₂ K₃ : DerivedCategory 𝒜} (φ : K₁ ⟶ K₂) (ψ : K₂ ⟶ K₃)
    (hK₁LE : K₁.IsLE 0) (hK₃GE : K₃.IsGE (-1))
    (hφ : (DerivedCategory.homologyFunctor 𝒜 0).map φ = 0)
    (hψ : (DerivedCategory.homologyFunctor 𝒜 (-1)).map ψ = 0) =>
  (CategoryTheory.DerivedCategory.TwoTerm.comp_eq_zero_of_homologyMap_eq_zero
      φ ψ hK₁LE hK₃GE hφ hψ : φ ≫ ψ = 0)
