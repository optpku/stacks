module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Sites.FilteredColimits.Cardinal

/-!
# Ordinal-indexed colimits of sheaves

The core ordinal statement is formulated for a coverage.  A separate precoverage bridge retains
the source presentation without exposing its pullback and base-change construction in the core
API.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory.Sites.FilteredColimitSections

variable {C : Type u} [Category.{v} C] {K : Coverage C}
variable [HasWeakSheafify K.toGrothendieck (Type (max u v))]

/-- Lemma 7.17.10 (0GS0), at the coverage layer: for an ordinal-indexed system of sheaves,
sections commute with the colimit when every covering presieve has raw arrow type of cardinality
strictly below `β.cof`.  The equivalent chosen-generating-family formulation is available through
`Precoverage.hasCardinalLTGeneratingFamilies_iff`. -/
@[stacks 0GS0]
theorem isIso_of_ordinal
    (β : Ordinal.{max u v})
    (F : Set.Iio β ⥤ Sheaf K.toGrothendieck (Type (max u v))) (U : C)
    [HasColimit F]
    [HasColimit
      (F ⋙ (sheafSections K.toGrothendieck (Type (max u v))).obj (op U))]
    [HasColimit (F ⋙ sheafToPresheaf K.toGrothendieck (Type (max u v)))]
    (hK : K.hasCardinalLTCoveringPresieves β.cof) :
    IsIso (comparison F U) := sorry

end CategoryTheory.Sites.FilteredColimitSections

namespace CategoryTheory.Precoverage.FilteredColimitSections

variable {C : Type u} [Category.{v} C] {K : Precoverage C}
variable [K.HasPullbacks] [K.IsStableUnderBaseChange]
variable [HasWeakSheafify K.toCoverage.toGrothendieck (Type (max u v))]

/-- Lemma 7.17.10 (0GS0), in a precoverage presentation: this bridge applies the coverage-level
ordinal comparison to `K.toCoverage`. -/
@[stacks 0GS0]
theorem isIso_of_ordinal
    (β : Ordinal.{max u v})
    (F : Set.Iio β ⥤ Sheaf K.toCoverage.toGrothendieck (Type (max u v))) (U : C)
    [HasColimit F]
    [HasColimit
      (F ⋙ (sheafSections K.toCoverage.toGrothendieck (Type (max u v))).obj (op U))]
    [HasColimit (F ⋙ sheafToPresheaf K.toCoverage.toGrothendieck (Type (max u v)))]
    (hK : K.hasCardinalLTCoveringPresieves β.cof) :
    IsIso (Sites.FilteredColimitSections.comparison F U) := sorry

/-- Lemma 7.17.10 (0GS0), in the literal set-level form: the ordinal section-comparison map is
bijective under the cardinally bounded precoverage hypothesis.  The coverage-level `IsIso` theorem
is the categorical owner; this is its `Type`-valued source-facing companion. -/
@[stacks 0GS0]
theorem bijective_of_ordinal
    (β : Ordinal.{max u v})
    (F : Set.Iio β ⥤ Sheaf K.toCoverage.toGrothendieck (Type (max u v))) (U : C)
    [HasColimit F]
    [HasColimit
      (F ⋙ (sheafSections K.toCoverage.toGrothendieck (Type (max u v))).obj (op U))]
    [HasColimit (F ⋙ sheafToPresheaf K.toCoverage.toGrothendieck (Type (max u v)))]
    (hK : K.hasCardinalLTCoveringPresieves β.cof) :
    Function.Bijective (Sites.FilteredColimitSections.comparison F U) := sorry

end CategoryTheory.Precoverage.FilteredColimitSections
