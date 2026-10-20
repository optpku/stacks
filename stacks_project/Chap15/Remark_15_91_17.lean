/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.Replacement
import StacksCheckRecall

/-!
# Remark 15.91.17

The canonical cycles module replaces an arbitrary module by a glueable one
without changing its base change or its localization away from the
distinguished element.  The replacement map is surjective.

@stack 0BP9
-/

@[expose] public section

-- Remark 15.91.17 (1), the canonical replacement module and map.
@[stacks 0BP9 "(1) Beauville-Laszlo replacement module"]
#check @LocalizedModule.Away.BeauvilleLaszlo.replacement
#check @LocalizedModule.Away.BeauvilleLaszlo.replacementMap

-- Remark 15.91.17 (2), glueability of the replacement.
@[stacks 0BP9 "(2) the replacement module is glueable"]
#check @LocalizedModule.Away.BeauvilleLaszlo.replacement_isGlueable

-- Remark 15.91.17 (3), invariance after base change.
@[stacks 0BP9 "(3) base-change bijectivity of the replacement map"]
#check @LocalizedModule.Away.BeauvilleLaszlo.replacementMap_baseChange_bijective

-- Remark 15.91.17 (4), invariance after localization away from `f`.
@[stacks 0BP9 "(4) localization bijectivity of the replacement map"]
#check @LocalizedModule.Away.BeauvilleLaszlo.replacementMap_localizedAway_bijective

-- Remark 15.91.17 (5), surjectivity before either scalar extension.
@[stacks 0BP9 "(5) surjectivity of the replacement map"]
#check @LocalizedModule.Away.BeauvilleLaszlo.replacementMap_surjective
