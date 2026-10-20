/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IndQuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic

/-!
# Ind-Quasi-Affine Scheme Morphisms

This file defines ind-quasi-affineness for scheme morphisms and the
compact-open quasi-affineness criterion used to characterize it.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

namespace Hom

/-- A scheme morphism is quasi-affine on compact opens if its restriction from
every quasi-compact open subscheme of its source is quasi-affine. -/
def IsQuasiAffineOnCompactOpens {X Y : Scheme.{u}} (g : X ⟶ Y) : Prop :=
  ∀ (U : X.Opens), IsCompact (U : Set X) → QuasiAffineHom (U.ι ≫ g)

/-- Quasi-affineness on compact opens is equivalent to its defining
restriction criterion. -/
theorem isQuasiAffineOnCompactOpens_iff {X Y : Scheme.{u}} (g : X ⟶ Y) :
    g.IsQuasiAffineOnCompactOpens ↔
      ∀ (U : X.Opens), IsCompact (U : Set X) → QuasiAffineHom (U.ι ≫ g) := sorry

end Hom

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- A scheme morphism is ind-quasi-affine if the inverse image of every affine
open subscheme of its target is ind-quasi-affine. -/
abbrev IndQuasiAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop :=
  targetAffineLocally
    (fun {Z T : Scheme} (_ : Z ⟶ T) ↦ Z.IsIndQuasiAffine) f

/-- Ind-quasi-affineness of a morphism is equivalent to ind-quasi-affineness
of the inverse images of all bundled affine opens of the target. -/
theorem indQuasiAffineHom_iff_affineOpens {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IndQuasiAffineHom f ↔
      ∀ V : Y.affineOpens, (f ⁻¹ᵁ (V : Y.Opens)).toScheme.IsIndQuasiAffine := sorry

end AlgebraicGeometry
