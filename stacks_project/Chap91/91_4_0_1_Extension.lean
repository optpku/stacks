/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Extension
public import ReasLib.CategoryTheory.Abelian.Extension.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Hom

variable {X X' : RingedSpace.{u}} (i : X ⟶ X')

namespace ModuleExtension

variable {i}

/-- The fixed-endpoint extension of the cokernel by the kernel associated to a
mixed-scalar module extension. -/
def extension (E : ModuleExtension i) :
    Extension ((pushforward i).obj E.kernel) ((pushforward i).obj E.cokernel) where
  E := E.middle
  f := E.ι
  g := E.π
  zero := E.zero
  shortExact := E.shortExact

/-- Rebuild a mixed-scalar module extension from a fixed-endpoint extension of
the cokernel by the kernel. -/
def ofExtension (kernel cokernel : X.Modules)
    (E : Extension ((pushforward i).obj kernel) ((pushforward i).obj cokernel)) :
    ModuleExtension i :=
  ModuleExtension.mk kernel cokernel E.E E.f E.g E.zero E.shortExact

/-- The underlying fixed-endpoint extension of the cokernel by the kernel. -/
abbrev toExtension (E : ModuleExtension i) :
    Extension ((pushforward i).obj E.kernel) ((pushforward i).obj E.cokernel) :=
  E.extension

end ModuleExtension

end AlgebraicGeometry.RingedSpace.Hom
