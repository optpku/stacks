/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal.Ringed
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.InternalHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal Module Sheaves on Ringed Spaces

The generic ringed-site construction cannot recover the commutative ring sheaf from the type
`X.Modules` during typeclass search.  This file installs the canonical ringed-space
specializations, using `X.sheaf` as the unambiguous owner of both structures.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The canonical monoidal structure on module sheaves over a ringed space. -/
@[stacks 03L6 "canonical tensor product on ringed-space modules", reducible]
noncomputable instance modulesMonoidalCategory (X : RingedSpace.{u}) :
    MonoidalCategory X.Modules :=
  SheafOfModules.RingedSite.moduleMonoidalCategory X.sheaf

/-- The canonical symmetry on module sheaves over a ringed space. -/
@[stacks 03L6 "canonical symmetry on ringed-space modules", reducible]
noncomputable instance modulesSymmetricCategory (X : RingedSpace.{u}) :
    SymmetricCategory X.Modules :=
  SheafOfModules.RingedSite.moduleSymmetricCategory X.sheaf

/-- The canonical closed monoidal structure on module sheaves over a ringed space. -/
noncomputable instance modulesMonoidalClosed (X : RingedSpace.{u}) :
    MonoidalClosed X.Modules :=
  SheafOfModules.RingedSite.InternalHom.moduleMonoidalClosed X.sheaf

end AlgebraicGeometry.RingedSpace
