/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.QuasiAffine

/-!
# Quasi-Affine Scheme Morphisms

This leaf owns the affine-target-local formulation of quasi-affine scheme
morphisms and its immediate separatedness and quasi-compactness consequences.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A scheme morphism is quasi-affine when the inverse image of every affine
open of its target is a quasi-affine scheme. -/
abbrev QuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  targetAffineLocally
    (fun {Y T : Scheme} (_ : Y ⟶ T) ↦ Y.IsQuasiAffine) f

/-- Unfold quasi-affineness using bundled affine opens of the target. -/
theorem quasiAffineHom_iff_affineOpens {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔
      ∀ U : S.affineOpens, (f ⁻¹ᵁ (U : S.Opens)).toScheme.IsQuasiAffine := sorry

/-- Unfold quasi-affineness using ordinary affine opens of the target. -/
theorem quasiAffineHom_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    QuasiAffineHom f ↔
      ∀ U : S.Opens, IsAffineOpen U → (f ⁻¹ᵁ U).toScheme.IsQuasiAffine := sorry

/-- A quasi-affine morphism is separated. -/
theorem QuasiAffineHom.isSeparated
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : QuasiAffineHom f) :
    IsSeparated f := sorry

/-- A quasi-affine morphism is quasi-compact. -/
theorem QuasiAffineHom.quasiCompact
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : QuasiAffineHom f) :
    QuasiCompact f := sorry

end AlgebraicGeometry
