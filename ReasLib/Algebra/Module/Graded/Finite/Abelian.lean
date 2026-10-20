/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Graded.Finite
public import ReasLib.Algebra.Module.Graded.Left.Abelian
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Abelian finitely generated graded modules

Finitely generated graded modules form an abelian full subcategory over a Noetherian ring.
-/

@[expose] public section

noncomputable section

universe x w v u

open CategoryTheory

namespace GradedModule.Left

variable {ι : Type x} [DecidableEq ι] [AddMonoid ι]
variable {κ : Type x} [DecidableEq κ] [AddAction ι κ]
variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {𝒜 : ι → Submodule R A} [GradedAlgebra 𝒜]

/-- Finitely generated graded modules contain a zero object. -/
instance instIsFGContainsZero : (isFG.{x, w, v, u} (κ := κ) 𝒜).ContainsZero := sorry

/-- Over a Noetherian ring, finitely generated graded modules are closed under kernels. -/
instance instIsFGClosedUnderKernels [IsNoetherianRing A] :
    (isFG.{x, w, v, u} (κ := κ) 𝒜).IsClosedUnderKernels := sorry

/-- Finitely generated graded modules are closed under cokernels. -/
instance instIsFGClosedUnderCokernels :
    (isFG.{x, w, v, u} (κ := κ) 𝒜).IsClosedUnderCokernels := sorry

/-- Finitely generated graded modules are closed under finite products. -/
instance instIsFGClosedUnderFiniteProducts :
    (isFG.{x, w, v, u} (κ := κ) 𝒜).IsClosedUnderFiniteProducts := sorry

/-- 052N: The full category of finitely generated left graded modules is abelian over a
Noetherian ring. -/
@[stacks 052N]
noncomputable instance instFGAbelian [IsNoetherianRing A] :
    Abelian (FG.{x, w, v, u} (κ := κ) 𝒜) := inferInstance

end GradedModule.Left
