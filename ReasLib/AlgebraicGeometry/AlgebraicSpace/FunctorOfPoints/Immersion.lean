/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-!
# Immersions of functors on schemes over an algebraic space

Relative representability with respect to `uliftYoneda`, with represented
pullbacks required to be immersions of schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is an immersion
when it is relatively representable with respect to `uliftYoneda` and every
represented pullback is an immersion of schemes. -/
def IsImmersionOnSchemesOver {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemeOver B) :=
    fun _ _ h ↦ AlgebraicGeometry.IsImmersion h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Immersions of `Type (u + 1)` functors on schemes over `B` are relatively
representable `uliftYoneda` morphisms whose represented scheme maps are
immersions. -/
theorem isImmersionOnSchemesOver_iff {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsImmersionOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.IsImmersion snd.left.left := sorry

end AlgebraicGeometry.AlgebraicSpace
