/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Quasicoherent.Coreflector.Exactness
public import Mathlib.CategoryTheory.Abelian.SerreClass.Localization

/-! # Serre localization by parasitic modules -/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Parasitic objects of `LQCohFbc X` form a Serre class. -/
instance LQCohFbc.parasitic_isSerreClass (X : GroupoidsOver S) [AlgebraicStack X] :
    IsSerreClass (LQCohFbc.parasitic X) := sorry

/-- The quasi-coherent coreflector is a localization at the morphisms that are
isomorphisms modulo parasitic objects. -/
instance LQCohFbc.toQCoh_isLocalization (X : GroupoidsOver S) [AlgebraicStack X] :
    (LQCohFbc.toQCoh X).IsLocalization (LQCohFbc.parasitic X).isoModSerre := sorry

end AlgebraicGeometry.GroupoidsOver
