module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Filtered.Final
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Denominator.Comma
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit

/-!
# Finality of denominator comparison functors

For a left calculus of fractions, target denominators are cofinal in the costructured-arrow
indexing category of the localization.  The dual source-denominator functor is initial under a
right calculus of fractions.  These canonical instances let downstream colimit and limit code use
the standard `Functor.Final` and `Functor.Initial` APIs without local instance reconstruction.
-/

@[expose] public section

universe v u vD uD

namespace CategoryTheory.MorphismProperty

open Limits

variable {C : Type u} [Category.{v} C]
variable {D : Type uD} [Category.{vD} D]

namespace Under

namespace toCostructuredArrow

/-- Every localization costructured arrow admits a morphism to a target-denominator stage. -/
theorem exists_hom (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    {X : C} (Y : CostructuredArrow S.Q (S.Q.obj X)) :
    ∃ U : MorphismProperty.Under S ⊤ X,
      Nonempty (Y ⟶ (MorphismProperty.Under.toCostructuredArrow S X).obj U) := sorry

/-- Parallel comparisons from a localization costructured arrow to one target-denominator stage
become equal after a further denominator refinement. -/
theorem exists_equalizer (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    {X : C} {Y : CostructuredArrow S.Q (S.Q.obj X)}
    (U : MorphismProperty.Under S ⊤ X)
    (f g : Y ⟶ (MorphismProperty.Under.toCostructuredArrow S X).obj U) :
    ∃ (V : MorphismProperty.Under S ⊤ X) (h : U ⟶ V),
      f ≫ (MorphismProperty.Under.toCostructuredArrow S X).map h =
        g ≫ (MorphismProperty.Under.toCostructuredArrow S X).map h := sorry

end toCostructuredArrow

/-- Target denominators are final in the localization costructured-arrow category. -/
@[stacks 05T5 "target denominators are final in the localization comma category"]
instance toCostructuredArrow_final (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) :
    Functor.Final (toCostructuredArrow S X) := sorry

/-- The localization costructured-arrow category is filtered when target denominators admit a
left calculus of fractions. -/
instance costructuredArrow_isFiltered (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) :
    IsFiltered (CostructuredArrow S.Q (S.Q.obj X)) := sorry

/-- A diagram on the localization costructured-arrow category has a colimit exactly when its
restriction to target denominators does. -/
theorem hasColimit_comp_iff (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    (X : C) (F : CostructuredArrow S.Q (S.Q.obj X) ⥤ D) :
    HasColimit (toCostructuredArrow S X ⋙ F) ↔ HasColimit F := sorry

end Under

namespace Over

namespace toStructuredArrow

/-- Every localization structured arrow receives a morphism from a source-denominator stage. -/
theorem exists_hom (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    {X : C} (Y : StructuredArrow (S.Q.obj X) S.Q) :
    ∃ U : MorphismProperty.Over S ⊤ X,
      Nonempty ((MorphismProperty.Over.toStructuredArrow S X).obj U ⟶ Y) := sorry

/-- Parallel comparisons from one source-denominator stage to a localization structured arrow
become equal after a further denominator refinement. -/
theorem exists_equalizer (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    {X : C} {Y : StructuredArrow (S.Q.obj X) S.Q}
    (U : MorphismProperty.Over S ⊤ X)
    (f g : (MorphismProperty.Over.toStructuredArrow S X).obj U ⟶ Y) :
    ∃ (V : MorphismProperty.Over S ⊤ X) (h : V ⟶ U),
      (MorphismProperty.Over.toStructuredArrow S X).map h ≫ f =
        (MorphismProperty.Over.toStructuredArrow S X).map h ≫ g := sorry

end toStructuredArrow

/-- Source denominators are initial in the localization structured-arrow category. -/
@[stacks 05T5 "source denominators are initial in the localization comma category"]
instance toStructuredArrow_initial (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) :
    Functor.Initial (toStructuredArrow S X) := sorry

/-- The localization structured-arrow category is cofiltered when source denominators admit a
right calculus of fractions. -/
instance structuredArrow_isCofiltered (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) :
    IsCofiltered (StructuredArrow (S.Q.obj X) S.Q) := sorry

/-- A diagram on the localization structured-arrow category has a limit exactly when its
restriction to source denominators does. -/
theorem hasLimit_comp_iff (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    (X : C) (F : StructuredArrow (S.Q.obj X) S.Q ⥤ D) :
    HasLimit (toStructuredArrow S X ⋙ F) ↔ HasLimit F := sorry

end Over



end CategoryTheory.MorphismProperty
