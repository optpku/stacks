/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.RegularSection.Stalk

/-!
# Affine criteria for regular structure-sheaf sections

This file characterizes regular global functions on schemes using all affine opens or one affine
open cover.
-/

@[expose] public section

open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- A global function is regular when its multiplication map on the structure module
is a monomorphism. -/
abbrev IsRegularStructureSection (f : Γ(X, ⊤)) : Prop :=
  RingedSpace.IsRegularSection (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)
    ((SheafOfModules.unit X.toRingedSpace.ringCatSheaf).unitHomEquiv
      (RingedSpace.globalSectionMul f (SheafOfModules.unit X.toRingedSpace.ringCatSheaf)))

/-- A global function on a scheme is a regular section of the structure module exactly when its
restriction is a nonzerodivisor on every affine open. -/
theorem isRegularStructureSection_iff_forall_affineOpen
    (f : Γ(X, ⊤)) :
    IsRegularStructureSection f ↔
      ∀ U : X.affineOpens,
        IsSMulRegular Γ(X, U)
          (X.presheaf.map (TopologicalSpace.Opens.leTop (U : X.Opens)).op f) := sorry

/-- A global function restricts to a nonzerodivisor on every affine open exactly when it does so
on every member of some affine open cover. -/
theorem forall_affineOpen_isSMulRegular_iff_exists_affineOpenCover
    (f : Γ(X, ⊤)) :
    (∀ U : X.affineOpens,
        IsSMulRegular Γ(X, U)
          (X.presheaf.map (TopologicalSpace.Opens.leTop (U : X.Opens)).op f)) ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀,
          IsSMulRegular Γ(X, (𝒰.f i).opensRange)
            (X.presheaf.map
              (TopologicalSpace.Opens.leTop ((𝒰.f i).opensRange)).op f) := sorry

end AlgebraicGeometry.Scheme
