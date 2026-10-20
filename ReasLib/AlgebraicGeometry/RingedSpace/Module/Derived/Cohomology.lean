/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Ordinary module cohomology on open subsets

This leaf supplies the comparison between module-valued cohomology obtained
from derived sections and ordinary cohomology of the underlying additive
sheaf. It is independent of a scheme structure or a base field.
-/

@[expose] public section

open CategoryTheory
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
variable [HasInjectiveResolutions X.Modules]

/-- Forgetting the `Γ(U, 𝒪_X)`-module structure on module cohomology over an
open subset recovers the cohomology object of the underlying additive sheaf. -/
@[stacks 01F1 "underlying module cohomology on an open"]
theorem moduleCohomologyAtOpenForget_obj_eq_underlyingSheafCohomology
    (U : Opens X.carrier) (F : X.Modules) (p : ℕ) :
    (forget₂ (ModuleCat (sectionsRingOnOpen X U)) AddCommGrpCat.{u}).obj
        (moduleCohomologyAtOpen U F p) =
      ((moduleUnderlyingSheaf X).obj F).H' p U := sorry



end AlgebraicGeometry.RingedSpace
