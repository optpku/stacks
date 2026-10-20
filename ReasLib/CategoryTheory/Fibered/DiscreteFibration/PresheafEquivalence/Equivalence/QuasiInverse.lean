/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Fibered.DiscreteFibration.PresheafEquivalence.Equivalence
public import ReasLib.CategoryTheory.Functor.Equivalence

/-!
# Specified quasi-inverses for the discrete Grothendieck correspondence

This leaf packages the explicit comparison isomorphisms as quasi-inverse data
and as equivalences of categories, retaining `toPresheaf` and `ofPresheaf` as
the specified inverse functors.
-/

@[expose] public section

universe w u v

namespace CategoryTheory

open Opposite

variable {C : Type u} [Category.{v} C]

namespace FiberedCategoryOver.Sets

namespace PresheafEquivalence

variable (C) in
/-- Explicit quasi-inverse data for the discrete Grothendieck construction. Its inverse is the
specified straightening functor `toPresheaf`, rather than an inverse selected from the
proposition that `ofPresheaf` is an equivalence. The base category is explicit because this
global choice has no value input from which Lean can recover it. -/
@[stacks 02Y2 "specified quasi-inverse to the Grothendieck construction"]
noncomputable def ofQuasiInverse :
    Functor.QuasiInverse
      (ofPresheaf C :
        (Cᵒᵖ ⥤ Type (max w u)) ⥤ FiberedCategoryOver.Sets.{u, v, max w u, v} C) where
  inverse := toPresheaf C
  unitIso := (PresheafEquivalence.ofIso C).symm
  counitIso := PresheafEquivalence.toIso C

/- Axiom audit: the inverse field is the named `toPresheaf` functor and the comparison fields are
the explicit natural isomorphisms in `PresheafEquivalence`. Deferred dependencies
occur only in their naturality and inverse-law proofs. -/

/-- The inverse stored by `ofQuasiInverse` is the specified straightening functor. -/
@[simp]
theorem ofQuasiInverse.inverse :
    (ofQuasiInverse C).inverse = toPresheaf C := sorry

/-- The unit stored by `ofQuasiInverse` is the inverse of the explicit presheaf-side
comparison. -/
@[simp]
theorem ofQuasiInverse.unitIso :
    (ofQuasiInverse C).unitIso =
      (PresheafEquivalence.ofIso C).symm := sorry

/-- The counit stored by `ofQuasiInverse` is the explicit discrete-fibration-side
comparison. -/
@[simp]
theorem ofQuasiInverse.counitIso :
    (ofQuasiInverse C).counitIso =
      PresheafEquivalence.toIso C := sorry

variable (C) in
/-- Explicit quasi-inverse data for straightening. It is obtained by reversing the specified
quasi-inverse data for `ofPresheaf`, so its inverse remains the named `ofPresheaf` functor. The
base category is explicit because this global choice has no value input from which Lean can
recover it. -/
@[stacks 02Y2 "specified quasi-inverse to straightening"]
noncomputable def toQuasiInverse :
    Functor.QuasiInverse
      (toPresheaf C :
        FiberedCategoryOver.Sets.{u, v, max w u, v} C ⥤ (Cᵒᵖ ⥤ Type (max w u))) :=
  (ofQuasiInverse C).symm

/-- The inverse stored by `toQuasiInverse` is the discrete Grothendieck construction. -/
@[simp]
theorem toQuasiInverse.inverse :
    (toQuasiInverse C).inverse = ofPresheaf C := sorry

/-- The unit stored by `toQuasiInverse` is the inverse of the explicit
discrete-fibration-side comparison. -/
@[simp]
theorem toQuasiInverse.unitIso :
    (toQuasiInverse C).unitIso =
      (PresheafEquivalence.toIso C).symm := sorry

/-- The counit stored by `toQuasiInverse` is the explicit presheaf-side comparison. -/
@[simp]
theorem toQuasiInverse.counitIso :
    (toQuasiInverse C).counitIso =
      PresheafEquivalence.ofIso C := sorry

variable (C) in
/-- The discrete Grothendieck construction and the specified straightening functor form an
equivalence of categories. This is the fixed-inverse owner for applications that need an actual
`≌`, while `ofQuasiInverse` retains the unadjusted two comparison isomorphisms. The base
category is explicit because this global equivalence has no value input from which Lean can
recover it. -/
@[stacks 02Y2 "specified discrete Grothendieck equivalence"]
noncomputable def ofEquivalence :
    (Cᵒᵖ ⥤ Type (max w u)) ≌ FiberedCategoryOver.Sets.{u, v, max w u, v} C :=
  (ofQuasiInverse C).adjointifyUnit

/-- The forward functor of `ofEquivalence` is the discrete Grothendieck construction. -/
@[simp]
theorem ofEquivalence.functor :
    (ofEquivalence C).functor = ofPresheaf C := sorry

/-- The inverse functor of `ofEquivalence` is the specified straightening functor. -/
@[simp]
theorem ofEquivalence.inverse :
    (ofEquivalence C).inverse = toPresheaf C := sorry

/-- The counit of `ofEquivalence` is the named discrete-fibration-side comparison. -/
@[simp]
theorem ofEquivalence.counitIso :
    (ofEquivalence C).counitIso =
      PresheafEquivalence.toIso C := sorry

/-- The unit of `ofEquivalence` is the canonical adjointification of the two specified comparisons.
The unadjusted presheaf-side comparison is retained by `ofQuasiInverse`. -/
theorem ofEquivalence.unitIso :
    (ofEquivalence C).unitIso =
      Equivalence.adjointifyη (PresheafEquivalence.ofIso C).symm
        (PresheafEquivalence.toIso C) := sorry

variable (C) in
/-- Straightening and the specified discrete Grothendieck construction form the reversed
equivalence of categories. The base category is explicit because this global equivalence has no
value input from which Lean can recover it. -/
@[stacks 02Y2 "specified straightening equivalence"]
noncomputable def toEquivalence :
    FiberedCategoryOver.Sets.{u, v, max w u, v} C ≌ (Cᵒᵖ ⥤ Type (max w u)) :=
  (toQuasiInverse C).adjointifyUnit

/-- The forward functor of `toEquivalence` is the specified straightening functor. -/
@[simp]
theorem toEquivalence.functor :
    (toEquivalence C).functor = toPresheaf C := sorry

/-- The inverse functor of `toEquivalence` is the discrete Grothendieck construction. -/
@[simp]
theorem toEquivalence.inverse :
    (toEquivalence C).inverse = ofPresheaf C := sorry

/-- The counit of `toEquivalence` is the named presheaf-side comparison. -/
@[simp]
theorem toEquivalence.counitIso :
    (toEquivalence C).counitIso =
      PresheafEquivalence.ofIso C := sorry

/-- The unit of `toEquivalence` is the canonical adjointification of the reversed
specified comparisons. -/
theorem toEquivalence.unitIso :
    (toEquivalence C).unitIso =
      Equivalence.adjointifyη (PresheafEquivalence.toIso C).symm
        (PresheafEquivalence.ofIso C) := sorry

end PresheafEquivalence

end FiberedCategoryOver.Sets

end CategoryTheory
