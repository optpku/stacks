/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.FGModuleCat.FiniteProducts

/-!
# Finite products and the zero object in `FGModuleCat`

Finitely generated modules are closed under finite products over an arbitrary
ring, so `FGModuleCat` has finite products and a zero object without a
Noetherian hypothesis.
-/

@[expose] public section

open CategoryTheory Limits

universe u v

namespace FGModuleCat

variable (R : Type u) [Ring R]

/- Finite products exist in `FGModuleCat R` for an arbitrary ring `R`. -/
#check (FGModuleCat.instHasFiniteProducts R : HasFiniteProducts (FGModuleCat.{v} R))

/- The zero object of `FGModuleCat R` is the zero module. -/
#check (FGModuleCat.instHasZeroObject R : HasZeroObject (FGModuleCat.{v} R))

/- The finitely generated zero module is a zero object of `FGModuleCat R`. -/
#check (FGModuleCat.isZero_ofPUnit R : IsZero (of R (PUnit : Type v)))

end FGModuleCat
