/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Fiber

/-!
# Immersions of functors on schemes over an algebraic space

Relative representability of morphisms of `Type (u + 1)` functors on
`SchemeOver B` with respect to `uliftYoneda`, with represented pullbacks
required to be immersions of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/- Immersion representability on schemes over an algebraic space. -/
#check (AlgebraicGeometry.AlgebraicSpace.IsImmersionOnSchemesOver :
  {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} → (F ⟶ G) → Prop)

/- Relative representability and the immersion condition on represented pullbacks. -/
#check (AlgebraicGeometry.AlgebraicSpace.isImmersionOnSchemesOver_iff :
  ∀ {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G),
    IsImmersionOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.IsImmersion snd.left.left)

end AlgebraicGeometry.AlgebraicSpace
