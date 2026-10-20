/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.BigZariski.Representability

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.15.4: a Zariski sheaf covered by representable Zariski-open
subfunctors is representable. -/
@[stacks 01JJ]
#check Scheme.LocalRepresentability.isRepresentable_of_zariskiOpen_subfunctor_cover

#check Scheme.LocalRepresentability.isRepresentable_of_subfunctor_cover
#check Scheme.LocalRepresentability.isRepresentable_of_locallySurjective_subfunctors

/- With an explicit representable open atlas, Mathlib retains the glued scheme and its full
representing equivalence rather than discarding them into `IsRepresentable`. -/
#check Scheme.LocalRepresentability.glueData
#check Scheme.LocalRepresentability.representableBy
