/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import StacksCheckRecall

@[expose] public section

/- `SheafOfModules.IsQuasicoherent` is the canonical owner for the setting referenced by the
source. The scheme and topos closed-immersion predicates assert properties absent from this
editorial remark, so a tagged check avoids both semantic drift and a redundant local wrapper. -/

/- Remark 6.32.6: the relationship between closed immersions and ringed spaces is deferred to the
setting of quasi-coherent sheaves. Mathlib's canonical predicate for that setting is
`SheafOfModules.IsQuasicoherent`; this editorial remark asserts no closed-immersion theorem to
formalize in this chapter. -/
@[stacks 00AJ "closed immersions of ringed spaces are deferred to quasi-coherent sheaves"]
#check SheafOfModules.IsQuasicoherent
