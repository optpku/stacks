/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration.FilteredColimit
import StacksCheckRecall

/-!
@stack 08Q5
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

universe u w w'

namespace SSet.modelCategoryQuillen.I

variable {J : Type w'} [Category.{w} J] [IsFiltered J]
variable (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c)
variable (hF : ∀ j, I.rlp ((F.obj j).hom))

/- Lemma 14.30.7 (08Q5), canonical form: trivial Kan fibrations are stable under filtered
colimits as a morphism property. -/
@[stacks 08Q5 "morphism-property form"]
#check (I.rlp.filteredColimits :
  MorphismProperty.IsStableUnderFilteredColimits.{w, w'} I.rlp)

/- Lemma 14.30.7 (08Q5), source-facing form: the arrow at the point of a colimiting filtered
cocone is a trivial Kan fibration when every stage is. -/
@[stacks 08Q5 "arrow-cocone form"]
#check (I.rlp.filteredColimit F c hc hF : I.rlp c.pt.hom)

end SSet.modelCategoryQuillen.I
