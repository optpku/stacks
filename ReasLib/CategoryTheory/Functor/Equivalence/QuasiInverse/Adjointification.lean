/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic

/-!
# Adjointification of explicit quasi-inverses

This file turns quasi-inverse data into mathlib equivalences and records independence of the
chosen inverse functor.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.Functor.QuasiInverse

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]
variable {F : A ⥤ B}

/-- Adjointify the unit of explicit quasi-inverse data to obtain mathlib's canonical equivalence.

`CategoryTheory.Equivalence` includes a triangle identity, whereas `QuasiInverse` deliberately
records only the two inverse comparisons. Accordingly, `Equivalence.mk` retains the supplied
forward functor, inverse functor, and counit, and adjointifies the unit. -/
@[stacks 019F "adjointification of an explicit quasi-inverse unit"]
def adjointifyUnit (e : QuasiInverse F) : A ≌ B :=
  Equivalence.mk F e.inverse e.unitIso e.counitIso

/-- Adjointifying the unit retains the original forward functor. -/
@[simp, stacks 019F "forward functor after unit adjointification"]
theorem adjointifyUnit.functor (e : QuasiInverse F) :
    e.adjointifyUnit.functor = F := sorry

/-- Adjointifying the unit retains the supplied inverse functor. -/
@[simp, stacks 019F "inverse functor after unit adjointification"]
theorem adjointifyUnit.inverse (e : QuasiInverse F) :
    e.adjointifyUnit.inverse = e.inverse := sorry

/-- Adjointifying the unit retains the supplied counit isomorphism. -/
@[simp, stacks 019F "counit after unit adjointification"]
theorem adjointifyUnit.counitIso (e : QuasiInverse F) :
    e.adjointifyUnit.counitIso = e.counitIso := sorry

/-- The new unit is mathlib's canonical adjointification of the supplied comparisons. -/
@[stacks 019F "canonical unit after adjointification"]
theorem adjointifyUnit.unitIso (e : QuasiInverse F) :
    e.adjointifyUnit.unitIso =
      Equivalence.adjointifyη e.unitIso e.counitIso := sorry

/-- Adjointify the counit of explicit quasi-inverse data while retaining the supplied unit.

This is the symmetric counterpart of `adjointifyUnit`: reverse the quasi-inverse data,
adjointify its unit, and reverse the resulting equivalence. -/
@[stacks 019F "adjointification of an explicit quasi-inverse counit"]
def adjointifyCounit (e : QuasiInverse F) : A ≌ B :=
  e.symm.adjointifyUnit.symm

/-- Adjointifying the counit retains the original forward functor. -/
@[simp, stacks 019F "forward functor after counit adjointification"]
theorem adjointifyCounit.functor (e : QuasiInverse F) :
    e.adjointifyCounit.functor = F := sorry

/-- Adjointifying the counit retains the supplied inverse functor. -/
@[simp, stacks 019F "inverse functor after counit adjointification"]
theorem adjointifyCounit.inverse (e : QuasiInverse F) :
    e.adjointifyCounit.inverse = e.inverse := sorry

/-- Adjointifying the counit retains the supplied unit isomorphism. -/
@[simp, stacks 019F "unit after counit adjointification"]
theorem adjointifyCounit.unitIso (e : QuasiInverse F) :
    e.adjointifyCounit.unitIso = e.unitIso := sorry

/-- The new counit is the symmetric canonical adjointification of the supplied comparisons. -/
@[stacks 019F "canonical counit after adjointification"]
theorem adjointifyCounit.counitIso (e : QuasiInverse F) :
    e.adjointifyCounit.counitIso =
      (Equivalence.adjointifyη e.counitIso.symm e.unitIso.symm).symm := sorry

end CategoryTheory.Functor.QuasiInverse
