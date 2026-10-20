/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.GlobalSections.KernelIdeal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel ideals on target opens

For a morphism of locally ringed spaces, the ideal on a target open is the kernel of the
corresponding component of the structure-sheaf map. This is the intrinsic owner of the affine
chart ideal and does not require selecting a restriction morphism.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

/-- The kernel ideal of the structure-sheaf map on a target open. -/
@[stacks 01IN "kernel ideal on a target open"]
noncomputable def kernelIdealOnOpen
    {X Z : LocallyRingedSpace.{u}} (f : Z ⟶ X) (U : Opens X) :
    Ideal (X.presheaf.obj (op U)) :=
  RingHom.ker (f.c.app (op U)).hom

/-- Membership in the kernel ideal on an open is sectionwise vanishing under the structure-sheaf
map. -/
@[simp, stacks 01IN "kernel ideal membership on an open"]
theorem mem_kernelIdealOnOpen_iff
    {X Z : LocallyRingedSpace.{u}} (f : Z ⟶ X) (U : Opens X)
    (r : X.presheaf.obj (op U)) :
    r ∈ f.kernelIdealOnOpen U ↔ (f.c.app (op U)).hom r = 0 := sorry

/-- The canonical kernel ideal on an affine open of a scheme target. -/
@[stacks 01IN "affine-open kernel ideal"]
noncomputable abbrev affineOpenKernelIdeal
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (f : Z ⟶ X.toLocallyRingedSpace) (U : X.affineOpens) : Ideal Γ(X, U) :=
  f.kernelIdealOnOpen U.1

/-- Membership in an affine-open kernel ideal is sectionwise vanishing on that open. -/
@[simp, stacks 01IN "affine-open kernel membership criterion"]
theorem mem_affineOpenKernelIdeal_iff
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (f : Z ⟶ X.toLocallyRingedSpace) (U : X.affineOpens) (r : Γ(X, U)) :
    r ∈ f.affineOpenKernelIdeal U ↔
      (f.c.app (op U.1)).hom r = 0 := sorry

end AlgebraicGeometry.LocallyRingedSpace.Hom
