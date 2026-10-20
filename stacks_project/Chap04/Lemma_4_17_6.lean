/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Final.Connected
import StacksCheckRecall

@[expose] public section


open CategoryTheory.Limits

universe uI uJ uC vI vJ vC

namespace CategoryTheory

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable [IsConnected I]

section

variable (M : J ⥤ C)

/- The source specializes final-functor colimit invariance to the second projection. The verified
instance `final_snd` derives finality from exactly `[IsConnected I]`, and the owner pair
`Functor.Final.hasColimit_comp_iff` and `Functor.Final.colimitIso` supplies respectively the
existence equivalence and canonical comparison. Their specialization to `Prod.snd I J` recovers
the source without strengthening its hypotheses; keeping the standard owners exposes the usual
final-functor API to downstream arguments instead of adding projection-specific wrappers. -/

/- Lemma 4.17.6 (1): if `I` is connected, then a diagram `M : J ⥤ C` and its pullback along
`Prod.snd I J : I × J ⥤ J` have colimits simultaneously. -/
@[stacks 0A2B "colimit existence under a connected product projection"]
#check (Functor.Final.hasColimit_comp_iff (Prod.snd I J) :
  HasColimit (Prod.snd I J ⋙ M) ↔ HasColimit M)

variable [HasColimit M]

/- Lemma 4.17.6 (2): when these colimits exist, the canonical comparison identifies
`colimit (Prod.snd I J ⋙ M)` with `colimit M`. -/
@[stacks 0A2B "canonical colimit comparison for a connected product projection"]
#check (Functor.Final.colimitIso (Prod.snd I J) M :
  colimit (Prod.snd I J ⋙ M) ≅ colimit M)

end

end CategoryTheory
