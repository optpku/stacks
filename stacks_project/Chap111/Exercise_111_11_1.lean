/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.Algebra.Category.ModuleCat.Ext.AbelianGroup

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat

/- Exercise 111.11.1 (1): in the category of ℤ-modules, the groups
`Ext (ModuleCat.of ℤ ℤ) (ModuleCat.of ℤ ℤ) i` are additively equivalent to `ℤ` in degree `0`
and vanish for every positive `i`. -/
@[stacks 0CRC]
#check (ModuleCat.ext_int_int : ∀ i : ℕ,
    if i = 0 then
      Nonempty (Ext (of ℤ ℤ) (of ℤ ℤ) i ≃+ ℤ)
    else
      Subsingleton (Ext (of ℤ ℤ) (of ℤ ℤ) i))

/- Exercise 111.11.1 (2): in the category of ℤ-modules, the groups
`Ext (ModuleCat.of ℤ (ZMod 4)) (ModuleCat.of ℤ (ZMod 8)) i` are additively equivalent to
`ZMod 4` for `i ≤ 1` and vanish for every `i ≥ 2`. -/
@[stacks 0CRC]
#check (ModuleCat.ext_zmod4_zmod8 : ∀ i : ℕ,
    if i ≤ 1 then
      Nonempty (Ext (of ℤ (ZMod 4)) (of ℤ (ZMod 8)) i ≃+ ZMod 4)
    else
      Subsingleton (Ext (of ℤ (ZMod 4)) (of ℤ (ZMod 8)) i))

/- Exercise 111.11.1 (3): in the category of ℤ-modules, the groups
`Ext (ModuleCat.of ℤ ℚ) (ModuleCat.of ℤ (ZMod 2)) i` vanish for every `i`. -/
@[stacks 0CRC]
#check (ModuleCat.ext_rat_zmod2 : ∀ i : ℕ,
    Subsingleton (Ext (of ℤ ℚ) (of ℤ (ZMod 2)) i))

/- Exercise 111.11.1 (4): in the category of ℤ-modules, the groups
`Ext (ModuleCat.of ℤ (ZMod 2)) (ModuleCat.of ℤ (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))) i`
are additively equivalent to `ZMod 2` in degree `0` and vanish for every positive `i`. -/
@[stacks 0CRC]
#check (ModuleCat.ext_zmod2_ratModInt : ∀ i : ℕ,
    if i = 0 then
      Nonempty
        (Ext (of ℤ (ZMod 2)) (of ℤ (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))) i ≃+ ZMod 2)
    else
      Subsingleton
        (Ext (of ℤ (ZMod 2)) (of ℤ (ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ))) i))

end ModuleCat
