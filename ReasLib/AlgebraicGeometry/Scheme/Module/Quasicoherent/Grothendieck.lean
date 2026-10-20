/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CardinalGeneration.Small
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.CardinalGeneration

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The category of quasicoherent modules on a scheme is Grothendieck abelian. -/
instance instIsGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian (QCoh X) := sorry

/-- The inclusion of quasicoherent modules into all module sheaves has a right adjoint. -/
instance inclusionIsLeftAdjoint (X : Scheme.{u}) :
    (inclusion X).IsLeftAdjoint := sorry

end AlgebraicGeometry.Scheme.QCoh
