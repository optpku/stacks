/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Koszul.Monoid
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
import Mathlib.Tactic.CrossRefAttribute

/-!
# Koszul complexes on ringed spaces

The topology-independent Koszul complex and its commutative algebra structure are owned by
`SheafOfModules.RingedSite.Koszul`.  This file contains only the genuinely topological
specialization: the morphism from a finite free module sheaf to the structure sheaf determined by
global sections, and the corresponding Koszul complex and commutative algebra.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Koszul

variable {X : RingedSpace.{u}} {n : ℕ}

/-- The canonical morphism from the free rank-`n` module sheaf to `𝒪_X` determined by
a finite family of global sections of the structure sheaf. -/
@[stacks 062L "section map"]
noncomputable abbrev sectionMap
    (f : Fin n → (SheafOfModules.unit X.ringCatSheaf : X.Modules).sections) :=
  (SheafOfModules.unit X.ringCatSheaf : X.Modules).freeHomEquiv.symm
    (fun i : ULift.{u} (Fin n) ↦ f i.down)

/-- The Koszul complex associated to a finite family of global sections of the structure
sheaf of a ringed space. -/
@[stacks 062L]
noncomputable abbrev complexOfSections
    (f : Fin n → (SheafOfModules.unit X.ringCatSheaf : X.Modules).sections) :
    ChainComplex X.Modules ℕ :=
  SheafOfModules.RingedSite.Koszul.complex X.sheaf (sectionMap f)

/-- The commutative Koszul algebra attached to a finite family of global sections of the
structure sheaf. -/
@[stacks 062L "commutative Koszul algebra of global sections"]
noncomputable abbrev commMonOfSections
    (f : Fin n → (SheafOfModules.unit X.ringCatSheaf : X.Modules).sections) :
    CommMon (ChainComplex X.Modules ℕ) :=
  SheafOfModules.RingedSite.Koszul.commMon X.sheaf (sectionMap f)

/-- Forgetting the algebra structure on `commMonOfSections f` gives the Koszul complex of the
family `f`. -/
@[simp]
theorem commMonOfSections_X
    (f : Fin n → (SheafOfModules.unit X.ringCatSheaf : X.Modules).sections) :
    (commMonOfSections f).X = complexOfSections f := sorry

end AlgebraicGeometry.RingedSpace.Koszul
