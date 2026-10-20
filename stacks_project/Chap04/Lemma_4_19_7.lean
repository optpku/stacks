/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtered.ColimitComparisons
public import ReasLib.CategoryTheory.Filtered.ColimitComparisons.Counterexamples
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe vI uI

namespace CategoryTheory.Limits

variable {I : Type uI} [Category.{vI} I]
variable [HasSpanCocones I]

/-
The source assumes only `HasSpanCocones I`. Mathlib's
`MorphismProperty.IsStableUnderFilteredColimits (monomorphisms (Type _))` requires the stronger
`IsFiltered I`, including equalizers for parallel arrows. We therefore use the canonical
functor-level owner `Functor.PreservesMonomorphisms` under the exact source hypothesis. By
`NatTrans.mono_iff_mono_app` and `mono_iff_injective`, this packages precisely the source's
objectwise-injective conclusion and is reusable by later categorical statements. The independent
negative clause is a neutral existence theorem in
`Filtered.ColimitComparisons.Counterexamples`.
-/

/- Lemma 4.19.7 (1): if every span in `I` admits a commuting cocone, then the colimit functor on
`Type`-valued diagrams preserves monomorphisms, equivalently objectwise injective natural
transformations induce injective maps on colimits. -/
@[stacks 09WT "Type-valued colimits preserve objectwise injectivity"]
#check (colim.preservesMonomorphisms_of_hasSpanCocones (I := I) :
  (colim : (I ⥤ Type (max uI vI)) ⥤ Type (max uI vI)).PreservesMonomorphisms)

/- Lemma 4.19.7 (2): the analogous assertion is false for diagrams of abelian groups: there is
an index category with commuting span cocones and an objectwise injective natural transformation
whose induced map on colimits is not injective. -/
@[stacks 09WT "counterexample for abelian-group-valued colimits"]
#check (AddCommGrpCat.colim.exists_map_not_injective :
  ∃ (J : Type) (_ : Category J) (_ : HasSpanCocones J)
    (M N : J ⥤ AddCommGrpCat) (alpha : M ⟶ N),
      (∀ j : J, Function.Injective (alpha.app j)) ∧
        ¬ Function.Injective (colim.map alpha))

end CategoryTheory.Limits
