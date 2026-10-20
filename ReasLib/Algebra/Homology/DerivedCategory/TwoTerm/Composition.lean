/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition of maps between two-term derived objects

The source and target homology conditions occur in different degrees, so this vanishing result is
kept as a dedicated composition lemma rather than folded into an endomorphism criterion.

@stack 0AJT
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe w v u

namespace CategoryTheory.DerivedCategory.TwoTerm

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasDerivedCategory.{w} 𝒜]

local notation "D" => _root_.DerivedCategory 𝒜
local notation "H" => _root_.DerivedCategory.homologyFunctor 𝒜

/-- Lemma 15.85.11 (Stacks `0AJT`): if `K₁` has no homology in degrees above `0`, `K₃` has
no homology in degrees below `-1`, `φ : K₁ ⟶ K₂` induces zero on `H⁰`, and
`ψ : K₂ ⟶ K₃` induces zero on `H⁻¹`, then `φ ≫ ψ = 0`. -/
@[stacks 0AJT "composition vanishing for two-term derived objects"]
theorem comp_eq_zero_of_homologyMap_eq_zero
    {K₁ K₂ K₃ : D} (φ : K₁ ⟶ K₂) (ψ : K₂ ⟶ K₃)
    (hK₁LE : K₁.IsLE 0) (hK₃GE : K₃.IsGE (-1))
    (hφ : (H 0).map φ = 0) (hψ : (H (-1)).map ψ = 0) :
    φ ≫ ψ = 0 := sorry
/- Proof strategy: factor `φ` through `t.truncLE (-1)` using `hφ` and factor `ψ` through
`t.truncGE 0` using `hψ`.  The support assumptions place these two intermediate objects on
opposite sides of the t-structure, so the middle morphism vanishes by orthogonality. -/

end CategoryTheory.DerivedCategory.TwoTerm
