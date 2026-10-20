/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 18.40.6 (04H8): a site-presented ringed topos is locally ringed exactly when its
structure sheaf carries the canonical locally ringed predicate. -/
@[stacks 04H8]
#check @Sheaf.IsLocallyRinged
