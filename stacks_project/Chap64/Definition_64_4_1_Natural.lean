/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Ring.CommutatorQuotient

universe u

variable (R : Type u) [NonUnitalNonAssocRing R]

#check (Ring.CommutatorQuotient.mk : R →+ Ring.CommutatorQuotient R)
