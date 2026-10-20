/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.Limit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 37.76.9: a weighting on the base change of a quasi-finite finitely presented
affine morphism to a directed affine limit descends to every sufficiently late stage. -/
@[stacks 0F3P] #check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.exists_eventually_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ i, IsAffine (D.obj i)] (i₀ : I)
      {X₀ : Scheme.{u}} [IsAffine X₀] (f₀ : X₀ ⟶ D.obj i₀)
      [QuasiFinite f₀] [FinitePresentation f₀]
      {w : (Scheme.baseChangeOverCone D c i₀ f₀).pt → ℤ},
      (hw : (pullback.fst (c.π.app i₀) f₀).IsWeighting w) →
      ∃ (i₁ : I) (h₀₁ : i₀ ≤ i₁), ∀ ⦃i : I⦄, (h₁ᵢ : i₁ ≤ i) →
        let h₀ᵢ : i₀ ≤ i := h₀₁.trans h₁ᵢ
        let fᵢ := pullback.fst (D.map (homOfLE h₀ᵢ)) f₀
        let kᵢ := (Scheme.baseChangeOverCone D c i₀ f₀).π.app
          (Over.mk (homOfLE h₀ᵢ))
        ∃ wᵢ : (Scheme.baseChangeOverDiagram D i₀ f₀).obj
            (Over.mk (homOfLE h₀ᵢ)) → ℤ,
          fᵢ.IsWeighting wᵢ ∧ (fun x ↦ wᵢ (kᵢ x)) = w)

end AlgebraicGeometry.Scheme.Hom
