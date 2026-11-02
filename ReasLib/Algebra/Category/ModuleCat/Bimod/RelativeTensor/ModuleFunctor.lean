/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Bimod.RelativeTensor.Functor

/-!
# Relative tensor functors on ordinary modules

For a fixed bimodule `K`, tensoring right `A`-modules over `A` with `K` gives
a functor to right `B`-modules.
-/

@[expose] public section

open CategoryTheory

universe u v w x

namespace Module.Bimodule.RelativeTensor

variable {R : Type u} {A : Type v} {B : Type w} (K : Type x)
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup K] [Module R K] [Module A K] [Module Bᵐᵒᵖ K]
variable [IsScalarTower R A K] [IsScalarTower R Bᵐᵒᵖ K]
variable [SMulCommClass A Bᵐᵒᵖ K]

/-- Tensoring right `A`-modules over `A` with a fixed `(A, B)`-bimodule `K`.
-/
noncomputable abbrev tensorModuleFunctor :
    ModuleCat.{x} Aᵐᵒᵖ ⥤ ModuleCat.{x} Bᵐᵒᵖ :=
  RelativeTensor.functor (R := R) (A := A) (B := B) K

end Module.Bimodule.RelativeTensor
