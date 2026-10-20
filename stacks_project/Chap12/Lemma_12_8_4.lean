/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.MorphismProperty.Localization.Abelian
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory

open MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
variable (W : MorphismProperty C)

section Left

variable [W.HasLeftCalculusOfFractions]

/- Lemma 12.8.4 (1): a left-fraction localization has cokernels and `Q` preserves them. -/
#check (inferInstance : HasCokernels W.Localization)
#check MorphismProperty.Localization.Q_preservesCokernel W

end Left

section Right

variable [W.HasRightCalculusOfFractions]

/- Lemma 12.8.4 (2): a right-fraction localization has kernels and `Q` preserves them. -/
#check (inferInstance : HasKernels W.Localization)
#check MorphismProperty.Localization.Q_preservesKernel W

end Right

section Multiplicative

variable [W.HasLeftCalculusOfFractions] [W.HasRightCalculusOfFractions]

/- Lemma 12.8.4 (3): a two-sided localization is abelian and its localization functor is exact. -/
#check (inferInstance : Abelian W.Localization)

@[stacks 05QG]
#check MorphismProperty.Localization.Q_exact W

end Multiplicative

end CategoryTheory
