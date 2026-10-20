/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.TrivialKanFibration
public import ReasLib.AlgebraicTopology.SimplicialSet.Arrow.Presentable
public import ReasLib.CategoryTheory.MorphismProperty.LiftingProperty.FilteredColimit
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08Q5

# Filtered colimits of trivial Kan fibrations

The boundary-inclusion right lifting property is stable under filtered colimits. The result is
exposed both as the canonical morphism-property instance and as an arrow-cocone eliminator.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SSet.modelCategoryQuillen

universe u w w'

namespace SSet.modelCategoryQuillen.I

/-- Every boundary-inclusion test in `I` is a compact arrow of simplicial sets. This is the thin
specialization of `SSet.Arrow.compact`; bundling the test as an element of `I.toSet` keeps the
boundary dimension, endpoints, and membership proof implicit. -/
@[stacks 08Q5 "compactness of boundary-inclusion arrows"]
theorem arrowCompact (i : I.toSet) :
    PreservesFilteredColimitsOfSize.{w, w'}
      (coyoneda.obj (Opposite.op i.1)) := sorry

namespace rlp

/-- The boundary-inclusion right lifting property is stable under filtered colimits. -/
@[stacks 08Q5 "filtered-colimit stability of trivial Kan fibrations"]
instance filteredColimits :
    MorphismProperty.IsStableUnderFilteredColimits.{w, w'} I.rlp := sorry

/-- The point of a filtered-colimit cocone of morphisms in `I.rlp` again lies in `I.rlp`. -/
@[stacks 08Q5 "arrow-cocone form"]
theorem filteredColimit
    {J : Type w'} [Category.{w} J] [IsFiltered J]
    (F : J ⥤ Arrow SSet.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, I.rlp ((F.obj j).hom)) :
    I.rlp c.pt.hom := sorry

end rlp

end SSet.modelCategoryQuillen.I
