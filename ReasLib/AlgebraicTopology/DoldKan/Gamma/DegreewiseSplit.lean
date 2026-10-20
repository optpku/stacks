/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.Gamma.Additive
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import ReasLib.CategoryTheory.ShortComplex.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Applying `Γ₀` to degreewise split short complexes

A chosen splitting in each chain degree induces a chosen splitting after evaluating the
`Γ₀`-image in each simplicial degree.  The retraction and section are explicit maps assembled
from the canonical coproduct decomposition of `Γ₀`; only their splitting laws are proof debt.

@stack 0192
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u

namespace CategoryTheory.ShortComplex.DegreewiseSplitting

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteCoproducts C]
variable {S : ShortComplex (ChainComplex C ℕ)}

namespace mapΓ₀

/-- The pointwise retraction obtained by summing the chain-degree retractions over the canonical
coproduct decomposition of `Γ₀`. -/
@[stacks 0192 "Γ₀ retraction induced by a degreewise splitting"]
noncomputable def retraction (σ : DegreewiseSplitting S)
    (Δ : SimplexCategoryᵒᵖ) :
    (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ ⟶
      (AlgebraicTopology.DoldKan.Γ₀.obj S.X₁).obj Δ :=
  (AlgebraicTopology.DoldKan.Γ₀.splitting S.X₂).desc Δ fun a ↦
    (σ a.1.unop.len).r ≫
      ((AlgebraicTopology.DoldKan.Γ₀.splitting S.X₁).cofan Δ).inj a

/-- The pointwise section obtained by summing the chain-degree sections over the canonical
coproduct decomposition of `Γ₀`. -/
@[stacks 0192 "Γ₀ section induced by a degreewise splitting"]
noncomputable def section_ (σ : DegreewiseSplitting S)
    (Δ : SimplexCategoryᵒᵖ) :
    (AlgebraicTopology.DoldKan.Γ₀.obj S.X₃).obj Δ ⟶
      (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ :=
  (AlgebraicTopology.DoldKan.Γ₀.splitting S.X₃).desc Δ fun a ↦
    (σ a.1.unop.len).s ≫
      ((AlgebraicTopology.DoldKan.Γ₀.splitting S.X₂).cofan Δ).inj a

/-- The mapped first arrow followed by the induced retraction is the identity. -/
@[stacks 0192 "Gamma-zero degreewise splitting retraction law"]
theorem f_r (σ : DegreewiseSplitting S) (Δ : SimplexCategoryᵒᵖ) :
    (FunctorCategory.app
        (S.map AlgebraicTopology.DoldKan.Γ₀) Δ).f ≫
      retraction σ Δ = 𝟙 _ := sorry

/-- The induced section followed by the mapped second arrow is the identity. -/
@[stacks 0192 "Gamma-zero degreewise splitting section law"]
theorem s_g (σ : DegreewiseSplitting S) (Δ : SimplexCategoryᵒᵖ) :
    section_ σ Δ ≫
      (FunctorCategory.app
        (S.map AlgebraicTopology.DoldKan.Γ₀) Δ).g = 𝟙 _ := sorry

/-- The induced retraction and section decompose the identity after simplicial evaluation. -/
@[stacks 0192 "Gamma-zero degreewise splitting identity decomposition"]
theorem id (σ : DegreewiseSplitting S) (Δ : SimplexCategoryᵒᵖ) :
    (retraction σ Δ ≫
        ((FunctorCategory.app
            (S.map AlgebraicTopology.DoldKan.Γ₀) Δ).f :
          (AlgebraicTopology.DoldKan.Γ₀.obj S.X₁).obj Δ ⟶
            (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ) :
      (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ ⟶
        (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ) +
      (((FunctorCategory.app
          (S.map AlgebraicTopology.DoldKan.Γ₀) Δ).g :
          (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ ⟶
            (AlgebraicTopology.DoldKan.Γ₀.obj S.X₃).obj Δ) ≫
        section_ σ Δ :
      (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ ⟶
        (AlgebraicTopology.DoldKan.Γ₀.obj S.X₂).obj Δ) = 𝟙 _ := sorry

end mapΓ₀

/-- Applying `Γ₀` to a chosen degreewise splitting gives a chosen splitting after every
simplicial evaluation. -/
@[stacks 0192 "Γ₀ sends degreewise splittings to pointwise splittings"]
noncomputable def mapΓ₀ (σ : DegreewiseSplitting S) :
    FunctorCategory.PointwiseSplitting
      (S.map AlgebraicTopology.DoldKan.Γ₀) :=
  fun Δ ↦
    { r := mapΓ₀.retraction σ Δ
      s := mapΓ₀.section_ σ Δ
      f_r := mapΓ₀.f_r σ Δ
      s_g := mapΓ₀.s_g σ Δ
      id := mapΓ₀.id σ Δ }

namespace mapΓ₀

/-- A degreewise split row becomes short exact after applying `Γ₀` and evaluating in any
simplicial degree. -/
@[stacks 0192 "pointwise short exactness after Γ₀"]
theorem shortExactApp [HasZeroObject C] (σ : DegreewiseSplitting S)
    (Δ : SimplexCategoryᵒᵖ) :
    (FunctorCategory.app
      (S.map AlgebraicTopology.DoldKan.Γ₀) Δ).ShortExact := sorry

/-- Applying `Γ₀` to a degreewise split row in an abelian category gives a short exact row of
simplicial objects. -/
@[stacks 0192 "short exactness after applying Γ₀ to a degreewise split row"]
theorem shortExact {C : Type u} [Category.{v} C] [Abelian C]
    {S : ShortComplex (ChainComplex C ℕ)} (σ : DegreewiseSplitting S) :
    (S.map AlgebraicTopology.DoldKan.Γ₀).ShortExact := sorry

end mapΓ₀

end CategoryTheory.ShortComplex.DegreewiseSplitting
