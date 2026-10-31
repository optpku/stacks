/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

/-
Copyright (c) 2026 ReasLib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import ReasLib.AlgebraicGeometry.GroupScheme.Torsion.UniversalProperty

/-! # The bundled multiplication kernel

The category-of-groups view uses the already constructed group object on
the actual scheme fibre. It is shared by arbitrary-base group schemes and
legacy field-specific interfaces.
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry.Scheme.GroupObject

variable {S : Scheme.{u}} (G : Over S) [GrpObj G] [IsCommMonObj G]

/-- The canonical multiplication kernel, packaged as a group object. -/
def multiplicationKernelGroup (n : ℕ) : Grp (Over S) :=
  letI := multiplicationKernelGrpObj G n
  Grp.mk (multiplicationKernel G n)

@[simp]
theorem multiplicationKernelGroup_X (n : ℕ) :
    (multiplicationKernelGroup G n).X = multiplicationKernel G n := rfl

/-- The actual kernel inclusion, packaged as a morphism of group objects. -/
def kernelInclusionHom (n : ℕ) : multiplicationKernelGroup G n ⟶ Grp.mk G :=
  letI := multiplicationKernelGrpObj G n
  Grp.ofHom (kernelInclusion G n)

@[simp]
theorem kernelInclusionHom_hom_hom (n : ℕ) :
    (kernelInclusionHom G n).hom.hom = kernelInclusion G n := rfl

end AlgebraicGeometry.Scheme.GroupObject
