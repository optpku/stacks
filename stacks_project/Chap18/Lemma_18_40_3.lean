/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged.Point
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Lemma 18.40.3 (05D8) (1): local nontriviality makes every point stalk nontrivial. -/
@[stacks 05D8 "(1)"]
#check @Sheaf.nontrivial_stalk

/- Lemma 18.40.3 (05D8) (2): with enough points, nontrivial stalks detect the canonical
nontriviality-map isomorphism. -/
@[stacks 05D8 "(2)"]
#check @Sheaf.nontrivialityMap_isIso_iff_stalk_nontrivial
