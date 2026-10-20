/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat

/-- For every `i : ℕ`, the degree-`i` Ext group of `ℤ` with itself is
additively equivalent to `ℤ` in degree zero and subsingleton otherwise. -/
theorem ext_int_int (i : ℕ) :
    if i = 0 then
      Nonempty (Ext (of ℤ ℤ) (of ℤ ℤ) i ≃+ ℤ)
    else
      Subsingleton (Ext (of ℤ ℤ) (of ℤ ℤ) i) :=
  sorry

/-- For every `i : ℕ`, the degree-`i` Ext group from `ZMod 4` to `ZMod 8`
is additively equivalent to `ZMod 4` in degrees at most one and subsingleton
in higher degrees. -/
theorem ext_zmod4_zmod8 (i : ℕ) :
    if i ≤ 1 then
      Nonempty (Ext (of ℤ (ZMod 4)) (of ℤ (ZMod 8)) i ≃+ ZMod 4)
    else
      Subsingleton (Ext (of ℤ (ZMod 4)) (of ℤ (ZMod 8)) i) :=
  sorry

/-- For every `i : ℕ`, the degree-`i` Ext group from `ℚ` to `ZMod 2` is
subsingleton. -/
@[instance]
theorem ext_rat_zmod2 (i : ℕ) :
    Subsingleton (Ext (of ℤ ℚ) (of ℤ (ZMod 2)) i) :=
  sorry

/-- For every `i : ℕ`, the degree-`i` Ext group from `ZMod 2` to
`ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)` is additively equivalent to `ZMod 2`
in degree zero and subsingleton otherwise. -/
theorem ext_zmod2_ratModInt (i : ℕ) :
    if i = 0 then
      Nonempty
        (Ext (of ℤ (ZMod 2)) (of ℤ (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))) i ≃+ ZMod 2)
    else
      Subsingleton
        (Ext (of ℤ (ZMod 2)) (of ℤ (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))) i) :=
  sorry

end ModuleCat
