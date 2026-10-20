/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# Formally smooth scheme morphisms

A scheme morphism is formally smooth when all of its induced maps on compatible affine
coordinate rings are formally smooth.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A scheme morphism is formally smooth when every induced map on compatible affine
coordinate rings is formally smooth. -/
class FormallySmooth (f : X ⟶ Y) : Prop where
  /-- The induced ring map on compatible affine opens is formally smooth. -/
  formallySmooth_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V)
      (e : V ≤ f ⁻¹ᵁ U), (f.appLE U V e).hom.FormallySmooth

namespace Scheme.Hom

/-- Formal smoothness supplies formal smoothness of the induced map on compatible affine
coordinate rings. -/
alias formallySmooth_appLE := FormallySmooth.formallySmooth_appLE

end Scheme.Hom

namespace FormallySmooth

/-- Scheme-level formal smoothness is associated with ring-level formal smoothness. -/
instance instHasRingHomProperty :
    HasRingHomProperty (@FormallySmooth.{u}) RingHom.FormallySmooth := sorry

/-- A morphism of affine schemes is formally smooth if and only if its induced map on
global sections is formally smooth. -/
theorem iff_of_isAffine {X S : Scheme.{u}} (f : X ⟶ S) [IsAffine X] [IsAffine S] :
    FormallySmooth f ↔ f.appTop.hom.FormallySmooth := sorry

/-- Formally smooth scheme morphisms are stable under base change. -/
instance instIsStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange (@FormallySmooth.{u}) := sorry

/-- Formally smooth scheme morphisms are stable under composition. -/
instance instIsStableUnderComposition :
    MorphismProperty.IsStableUnderComposition (@FormallySmooth.{u}) := sorry

/-- The composite of two formally smooth scheme morphisms is formally smooth. -/
instance comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallySmooth f] [FormallySmooth g] : FormallySmooth (f ≫ g) := sorry

/-- Every smooth scheme morphism is formally smooth. -/
instance of_smooth [Smooth f] : FormallySmooth f := sorry

end FormallySmooth

end AlgebraicGeometry
