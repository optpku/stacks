/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints.Immersion

/-!
# Quasi-compact immersions of functors on schemes over an algebraic space

Relative representability of morphisms of `Type (u + 1)` functors on
`SchemeOver B` with respect to `uliftYoneda`, with represented pullbacks
required to be quasi-compact, or quasi-compact immersions, of schemes.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is quasi-compact
when it is relatively representable with respect to `uliftYoneda` and every
represented pullback is a quasi-compact morphism of schemes. -/
def IsQuasiCompactOnSchemesOver {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemeOver B) :=
    fun _ _ h ↦ AlgebraicGeometry.QuasiCompact h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Quasi-compact morphisms of `Type (u + 1)` functors on schemes over `B` are
relatively representable `uliftYoneda` morphisms whose represented scheme maps
are quasi-compact. -/
theorem isQuasiCompactOnSchemesOver_iff {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsQuasiCompactOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.QuasiCompact snd.left.left := sorry

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is a quasi-compact
immersion when it is relatively representable with respect to `uliftYoneda` and
every represented pullback is a quasi-compact immersion of schemes. -/
def IsQuasiCompactImmersionOnSchemesOver {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemeOver B) :=
    fun _ _ h ↦
      AlgebraicGeometry.QuasiCompact h.left.left ∧
        AlgebraicGeometry.IsImmersion h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Quasi-compact immersions of `Type (u + 1)` functors on schemes over `B` are
relatively representable `uliftYoneda` morphisms whose represented scheme maps
are quasi-compact immersions. -/
theorem isQuasiCompactImmersionOnSchemesOver_iff
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G) :
    IsQuasiCompactImmersionOnSchemesOver φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.QuasiCompact snd.left.left ∧
              AlgebraicGeometry.IsImmersion snd.left.left := sorry

/-- A morphism of functors on schemes over `B` is a quasi-compact immersion if
and only if it is both quasi-compact and an immersion in the `uliftYoneda`
relative sense. -/
theorem isQuasiCompactImmersionOnSchemesOver_iff_and
    {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)} (φ : F ⟶ G) :
    IsQuasiCompactImmersionOnSchemesOver φ ↔
      IsQuasiCompactOnSchemesOver φ ∧ IsImmersionOnSchemesOver φ := sorry

end AlgebraicGeometry.AlgebraicSpace
