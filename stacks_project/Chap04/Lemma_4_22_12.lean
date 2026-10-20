/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.CategoryTheory.Filtered.Final
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Final
import StacksCheckRecall

@[expose] public section

universe uI vI uJ vJ uC vC

namespace CategoryTheory

variable {I : Type uI} {J : Type uJ} {C : Type uC}
variable [Category.{vI} I] [Category.{vJ} J] [Category.{vC} C]

section

variable [IsFiltered I] [IsFiltered J]
variable (M : J ⥤ C)

/-
The source needs product filteredness and invariance of essential constancy under the second
projection. The canonical product instance and `CategoryTheory.IsFiltered.final_snd`, together
with `CategoryTheory.IsFiltered.IsEssentiallyConstant.iff_comp_final`, give these clauses exactly.
The checks below introduce no generalization: their category instances and diagram are precisely
the source inputs. Keeping the general final-functor theorem as the owner avoids a
projection-specific wrapper and lets downstream arguments reuse it for other final functors.
-/

/- Lemma 4.22.12 (1): the product `I × J` of filtered categories is filtered. -/
@[stacks 0A2C "filteredness of product index categories"] #check
  (inferInstance : IsFiltered (I × J))

/- Lemma 4.22.12 (2): a diagram `M : J ⥤ C` is essentially constant if and only if its
pullback along the projection `Prod.snd I J : I × J ⥤ J` is essentially constant. -/
@[stacks 0A2C "essential constancy under the second projection"] #check
  (IsFiltered.IsEssentiallyConstant.iff_comp_final (Prod.snd I J) M :
    IsFiltered.IsEssentiallyConstant M ↔
      IsFiltered.IsEssentiallyConstant (Prod.snd I J ⋙ M))

end

end CategoryTheory
