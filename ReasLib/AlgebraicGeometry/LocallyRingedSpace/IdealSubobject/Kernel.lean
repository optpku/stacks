/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Definition
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.IdealSubobject.Definition
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.Kernel
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Kernel ideals of locally ringed-space morphisms

This leaf specializes the kernel ideal of an arbitrary ringed-space morphism along
`LocallyRingedSpace.Hom.toShHom`; no closed-immersion hypothesis is required.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

namespace Hom

/-- The kernel ideal sheaf of a locally ringed-space morphism. -/
@[stacks 01HK "kernel ideal sheaf"]
noncomputable abbrev kernelIdealSheaf
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) :=
  RingedSpace.Hom.kernelIdealSheaf i.toShHom

/-- The kernel ideal subobject of a locally ringed-space morphism. -/
@[stacks 01HK "kernel ideal subobject"]
noncomputable abbrev kernelIdealSubobject
    {X Z : LocallyRingedSpace.{u}} (i : Z ⟶ X) : IdealSubobject X :=
  RingedSpace.Hom.kernelIdealSubobject i.toShHom

end Hom

end AlgebraicGeometry.LocallyRingedSpace
