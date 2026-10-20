/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Preserves.Over

/-!
# Forgetful functors and filtered colimits of commutative algebras

The forgetful functors from commutative algebras to commutative rings and to types preserve
filtered colimits whose indexing universe is bounded by the algebra universe.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace CommAlgCat.FilteredColimits

variable {k : Type u} [CommRing k]

namespace forget₂CommRing

/-- Forgetting a commutative `k`-algebra to a commutative ring preserves filtered colimits of the
specified size. -/
noncomputable instance preservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{v, v}
      (forget₂ (CommAlgCat.{u} k) CommRingCat.{u}) where
  preserves_filtered_colimits _ _ _ :=
    -- `forget₂` is `commAlgCatEquivUnder` followed by `Under.forget`, which preserves filtered
    -- colimits by mathlib's explicit cocone construction.
    preservesColimitsOfShape_of_natIso
      (F := (commAlgCatEquivUnder (.of k)).functor ⋙ Under.forget (CommRingCat.of k))
      (NatIso.ofComponents fun _ ↦ Iso.refl _)

end forget₂CommRing

namespace forgetToType

/-- Forgetting a commutative `k`-algebra to its carrier type preserves filtered colimits whose
index universe is bounded by the algebra universe. -/
noncomputable instance preservesFilteredColimitsOfSize [UnivLE.{v, u}] :
    PreservesFilteredColimitsOfSize.{v, v}
      (forget (CommAlgCat.{u} k)) :=
  haveI : PreservesFilteredColimitsOfSize.{v, v} (forget CommRingCat.{u}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u, u, v, v} _
  { preserves_filtered_colimits _ _ _ :=
      -- The carrier functor factors through the ring forgetful functor.
      preservesColimitsOfShape_of_natIso
        (F := forget₂ (CommAlgCat.{u} k) CommRingCat.{u} ⋙ forget CommRingCat.{u})
        (NatIso.ofComponents fun _ ↦ Iso.refl _) }

end forgetToType

end CommAlgCat.FilteredColimits
