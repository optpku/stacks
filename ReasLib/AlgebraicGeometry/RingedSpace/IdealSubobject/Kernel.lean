/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.KernelIdeal
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel ideal subobjects of ringed spaces

This leaf owns the kernel ideal of an arbitrary ringed-space morphism, independently of any
closed-immersion property.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

/-- The kernel ideal sheaf of a ringed-space morphism. -/
@[stacks 01C2 "kernel ideal sheaf"]
noncomputable abbrev kernelIdealSheaf
    {X Z : RingedSpace.{u}} (i : Z ⟶ X) : X.Modules :=
  SheafOfModules.RingedSite.KernelIdeal.sheaf.{u, u, u}
    (commRingSheafPushforwardMap i)

/-- The kernel ideal of a ringed-space morphism, retaining its canonical inclusion into the
target structure sheaf. -/
@[stacks 01C2 "kernel ideal subobject"]
noncomputable abbrev kernelIdealSubobject
    {X Z : RingedSpace.{u}} (i : Z ⟶ X) : X.IdealSubobject :=
  SheafOfModules.RingedSite.KernelIdeal.subobject.{u, u, u}
    (commRingSheafPushforwardMap i)

/-- The canonical inclusion of the kernel ideal sheaf into the target structure module. -/
@[stacks 01C2 "kernel ideal inclusion"]
noncomputable abbrev kernelIdealι
    {X Z : RingedSpace.{u}} (i : Z ⟶ X) :
    kernelIdealSheaf i ⟶ SheafOfModules.unit X.ringCatSheaf :=
  SheafOfModules.RingedSite.KernelIdeal.ι.{u, u, u}
    (commRingSheafPushforwardMap i)

/-- The module represented by the kernel ideal subobject is canonically the kernel ideal sheaf. -/
@[stacks 01C2 "kernel ideal representative comparison"]
noncomputable def kernelIdealIso
    {X Z : RingedSpace.{u}} (i : Z ⟶ X) :
    (kernelIdealSubobject i).toModule ≅ kernelIdealSheaf i :=
  Iso.refl _

/-- Under the canonical comparison, the subobject arrow is the kernel-ideal inclusion. -/
@[reassoc (attr := simp), stacks 01C2 "kernel ideal representative computation"]
theorem kernelIdealIso_hom_arrow
    {X Z : RingedSpace.{u}} (i : Z ⟶ X) :
    (kernelIdealIso i).hom ≫ kernelIdealι i =
      (kernelIdealSubobject i).arrow := sorry

end AlgebraicGeometry.RingedSpace.Hom
