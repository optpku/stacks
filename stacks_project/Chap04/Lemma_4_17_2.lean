/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Final
import StacksCheckRecall

@[expose] public section


open CategoryTheory CategoryTheory.Limits

universe vI uI vJ uJ vC uC

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]
variable {C : Type uC} [Category.{vC} C]
variable (H : I ⥤ J) [H.Final] (M : J ⥤ C)

/-
The source needs both the phrase “if either side exists” and the resulting object-level canonical
isomorphism. The verified owner pair `Functor.Final.hasColimit_comp_iff` and
`Functor.Final.colimitIso`, also used together in the nearby Lemmas 4.17.5 and 4.17.6, expresses
exactly those two aspects. The alternatives `Functor.Final.hasColimit_of_comp` and
`Functor.Final.colimit_pre_isIso` expose only one existence direction and the underlying
comparison-morphism instance. No generalization is introduced: mathlib's `Functor.Final` is the
source's cofinality hypothesis, and the two recalls recover the statement for every diagram while
providing downstream code with the standard existence and isomorphism APIs.
-/

/- Lemma 4.17.2 (1): for a final functor `H : I ⥤ J` and a diagram `M : J ⥤ C`, the colimit of
`H ⋙ M` exists if and only if the colimit of `M` exists. -/
@[stacks 04E7 "colimit existence is invariant under final precomposition"]
#check (Functor.Final.hasColimit_comp_iff H :
  HasColimit (H ⋙ M) ↔ HasColimit M)

section

variable [HasColimit M]

/- Lemma 4.17.2 (2): when these colimits exist, their canonical comparison is the isomorphism
`colimit (H ⋙ M) ≅ colimit M`. -/
@[stacks 04E7 "canonical colimit isomorphism under final precomposition"]
#check (Functor.Final.colimitIso H M : colimit (H ⋙ M) ≅ colimit M)

end
