/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.BaseChange
import StacksCheckRecall

@[expose] public section

/-!
# Remark 21.19.3

The canonical unbounded base-change morphism is owned by the ringed-site specialization of the
categorical mate construction.
-/

/- Remark 21.19.3 (07A7): a square of derived pullback functors induces the canonical mate
`L g^* (R f_* K) ⟶ R f'_* (L g'^* K)`. -/
@[stacks 07A7]
#check @RingedSite.Hom.DerivedBaseChange.map

#check @RingedSite.Hom.DerivedBaseChange.IsMap
#check @RingedSite.Hom.DerivedBaseChange.map_isMap
#check @RingedSite.Hom.DerivedBaseChange.map_spec
#check @RingedSite.Hom.DerivedBaseChange.IsMap.eq_map
