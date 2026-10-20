/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Equivalence.QuasiInverse.Basic

/-!
# Choosing explicit quasi-inverses

This file isolates the choice boundary between `Functor.IsEquivalence` and explicit
`Functor.QuasiInverse` data.
-/

@[expose] public section

universe vA uA vB uB

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A]
variable {B : Type uB} [Category.{vB} B]

/-- Package an explicit proof that a functor is an equivalence as mathlib's chosen equivalence.

Unlike `Functor.asEquivalence`, this bridge takes the proposition as ordinary data. This is the
appropriate interface when two independent criteria can prove equivalence and registering both
as global instances would create an overlapping typeclass path. -/
noncomputable def asEquivalenceOf (F : A ⥤ B) (h : F.IsEquivalence) : A ≌ B :=
  @Functor.asEquivalence _ _ _ _ F h

/-- The forward functor of the equivalence selected from an explicit equivalence proof is the
original functor. -/
@[simp]
theorem asEquivalenceOf.functor (F : A ⥤ B) (h : F.IsEquivalence) :
    (F.asEquivalenceOf h).functor = F := sorry

/-- Choose explicit quasi-inverse data for a functor carrying mathlib's canonical
`Functor.IsEquivalence` property. The choice boundary is exactly mathlib's `F.asEquivalence`;
consumers should use the projections below rather than unfold that construction. -/
noncomputable def asQuasiInverse (F : A ⥤ B) [F.IsEquivalence] :
    QuasiInverse F :=
  QuasiInverse.ofEquivalence F.asEquivalence

/-- Choose explicit quasi-inverse data from an equivalence proof supplied as an ordinary
argument. This avoids installing a proof-local instance at reuse sites. -/
noncomputable def asQuasiInverseOf (F : A ⥤ B) (h : F.IsEquivalence) :
    QuasiInverse F :=
  @asQuasiInverse _ _ _ _ F h

/-- The inverse selected from an explicit equivalence proof agrees with the inverse of the
corresponding bundled equivalence. -/
@[simp]
theorem asQuasiInverseOf.inverse (F : A ⥤ B) (h : F.IsEquivalence) :
    (F.asQuasiInverseOf h).inverse = (F.asEquivalenceOf h).inverse := sorry

/-- The unit selected from an explicit equivalence proof is the unit of the corresponding bundled
equivalence. -/
@[simp]
theorem asQuasiInverseOf.unitIso (F : A ⥤ B) (h : F.IsEquivalence) :
    (F.asQuasiInverseOf h).unitIso = (F.asEquivalenceOf h).unitIso := sorry

/-- The counit selected from an explicit equivalence proof is the counit of the corresponding
bundled equivalence. -/
@[simp]
theorem asQuasiInverseOf.counitIso (F : A ⥤ B) (h : F.IsEquivalence) :
    (F.asQuasiInverseOf h).counitIso = (F.asEquivalenceOf h).counitIso := sorry

/-- The inverse selected by `Functor.asQuasiInverse` is mathlib's canonical inverse functor. -/
@[simp]
theorem asQuasiInverse.inverse (F : A ⥤ B) [F.IsEquivalence] :
    F.asQuasiInverse.inverse = F.inv := sorry

/-- The unit selected by `Functor.asQuasiInverse` is the unit of mathlib's canonical
equivalence. -/
@[simp]
theorem asQuasiInverse.unitIso (F : A ⥤ B) [F.IsEquivalence] :
    F.asQuasiInverse.unitIso = F.asEquivalence.unitIso := sorry

/-- The counit selected by `Functor.asQuasiInverse` is the counit of mathlib's canonical
equivalence. -/
@[simp]
theorem asQuasiInverse.counitIso (F : A ⥤ B) [F.IsEquivalence] :
    F.asQuasiInverse.counitIso = F.asEquivalence.counitIso := sorry

/-- A functor is an equivalence exactly when it admits explicit quasi-inverse data. -/
theorem IsEquivalence.iff_nonempty_quasiInverse (F : A ⥤ B) :
    F.IsEquivalence ↔ Nonempty (QuasiInverse F) := sorry

end CategoryTheory.Functor
