/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo
import StacksCheckRecall

/-!
# 15.91.5.1

@stack 0F1Q
-/

@[expose] public section

section

variable {R : Type*} [CommRing R]
variable {R' : Type*} [CommRing R'] [Algebra R R']

/- Domain-style sampling for 15.91.5.1:
- primary domain: the Beauville-Laszlo Cech short complex in `ModuleCat R`;
- sampled owner declarations:
  `beauvilleLaszloCechLeftMap`,
  `beauvilleLaszloCechRightMap`,
  `beauvilleLaszloCech_comp_eq_zero`,
  `beauvilleLaszloCechSequence`;
- best owner abstraction: the packaged short-complex owner `beauvilleLaszloCechSequence`;
- primitive data: the left and right Cech maps together with their zero-composite relation;
- derived API: the resulting object of `ShortComplex (ModuleCat R)`;
- source/core/bridge triage:
  `source-facing`: the Beauville-Laszlo Cech sequence itself;
  `core/canonical`: `ShortComplex (ModuleCat R)` and `ModuleCat.shortComplexOfCompEqZero`;
  `bridge/view`: the upstream owner declaration `beauvilleLaszloCechSequence`, which this file
    recalls directly instead of reintroducing a local wrapper.
-/

/- 15.91.5.1: the Beauville-Laszlo Cech sequence attached to `R → R'` and `f`, viewed in the
canonical owner `ShortComplex (ModuleCat R)`, is
`beauvilleLaszloCechSequence (algebraMap R R') f`. -/
@[stacks 0F1Q "Beauville-Laszlo Cech sequence"]
#check beauvilleLaszloCechSequence

end
