/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeOver

/-! # Flat morphisms of presheaves on schemes over an algebraic space -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.SchemeOver

variable {S : Scheme.{u}} {B : AlgebraicSpace S}

/-- A morphism of `Type (u + 1)` functors on schemes over `B` is flat when it is
relatively representable with respect to `uliftYoneda` and every represented
pullback is a flat morphism of schemes. -/
def IsFlat {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) : Prop :=
  let P : MorphismProperty (SchemeOver B) :=
    fun _ _ h ↦ AlgebraicGeometry.Flat h.left.left
  P.relative uliftYoneda.{u + 1} φ

/-- Flatness of `Type (u + 1)` functors is relative representability for
`uliftYoneda` together with flatness of every represented scheme map. -/
theorem isFlat_iff {F G : (SchemeOver B)ᵒᵖ ⥤ Type (u + 1)}
    (φ : F ⟶ G) :
    IsFlat φ ↔
      uliftYoneda.{u + 1}.relativelyRepresentable φ ∧
        ∀ ⦃σ τ : SchemeOver B⦄ (ξ : uliftYoneda.{u + 1}.obj σ ⟶ G)
          (fst : uliftYoneda.{u + 1}.obj τ ⟶ F) (snd : τ ⟶ σ),
          IsPullback fst (uliftYoneda.{u + 1}.map snd) φ ξ →
            AlgebraicGeometry.Flat snd.left.left := sorry

end AlgebraicGeometry.AlgebraicSpace.SchemeOver
