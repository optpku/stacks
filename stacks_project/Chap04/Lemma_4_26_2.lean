module

public import ReasLib.CategoryTheory.ObjectProperty.FilteredColimitRestriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits Cardinal

universe w vC uC vD uD

-- Local instance justification (search instability): Mathlib intentionally keeps `ℵ₀`-regularity
-- out of global instance search. This source specialization mirrors the narrow registration used
-- by the ReasLib owner; making it global would pollute unrelated cardinal-filtered goals, while
-- exposing it as a theorem parameter would add no mathematical input to the `ℵ₀`-specific statement.
attribute [local instance] Cardinal.fact_isRegular_aleph0

namespace CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator

variable {C : Type uC} [Category.{vC} C]
variable {P : ObjectProperty C}
variable [LocallySmall.{w} C] [ObjectProperty.Small.{w} P]
variable (hP : P.IsCardinalFilteredGenerator (ℵ₀ : Cardinal.{w}))
variable (D : Type uD) [Category.{vD} D]
variable [HasFilteredColimitsOfSize.{w, w} C]
variable [HasFilteredColimitsOfSize.{w, w} D]

/- Lemma 4.26.2: restriction from filtered-colimit-preserving functors to a small full
subcategory of finitely presentable filtered generators is an equivalence. -/
@[stacks 0FWY]
#check (restrictionIsEquivalence hP D :
  Functor.IsEquivalence (filteredColimitRestriction.{w} P D))

end CategoryTheory.ObjectProperty.IsCardinalFilteredGenerator
