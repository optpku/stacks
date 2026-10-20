/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.GlobalSections.Linear
public import ReasLib.CategoryTheory.InverseSystem.Sequential
public import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology inverse systems on ringed spaces

This leaf specializes module cohomology to the top open and packages its application to a
sequential inverse system.  Limit and adic-topology arguments can therefore consume the resulting
module-valued tower without rebuilding the same top-open functor in chapter files.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

/-- Degree-`p` module cohomology on the whole ringed space, functorial in the module sheaf. -/
@[stacks 0EHA "module-valued global cohomology functor"]
noncomputable abbrev moduleCohomologyFunctor
    (X : RingedSpace.{u}) (p : ℕ) :
    X.Modules ⥤ ModuleCat.{u} (globalSectionsRing X) :=
  moduleCohomologyAtOpenFunctor X (⊤ : Opens X.carrier) p

/-- Degreewise global module cohomology is linear over the global-sections ring. -/
@[stacks 0EHA "linearity of module cohomology"]
noncomputable instance moduleCohomologyFunctor_linear
    (X : RingedSpace.{u}) (p : ℕ) :
    Functor.Linear (globalSectionsRing X) (moduleCohomologyFunctor X p) := sorry

/-- The module-valued degree-`p` cohomology tower of a sequential system of module sheaves. -/
@[stacks 0EHA "module-valued cohomology inverse system on a ringed space"]
noncomputable abbrev moduleCohomologyTower
    {X : RingedSpace.{u}} (F : SequentialInverseSystem X.Modules) (p : ℕ) :
    SequentialInverseSystem (ModuleCat.{u} (globalSectionsRing X)) :=
  F ⋙ moduleCohomologyFunctor X p

end AlgebraicGeometry.RingedSpace
