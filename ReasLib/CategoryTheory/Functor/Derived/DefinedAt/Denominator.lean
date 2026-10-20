module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.Transport
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Basic
public import ReasLib.CategoryTheory.MorphismProperty.Localization.Denominator.Final
public import ReasLib.CategoryTheory.MorphismProperty.Localization.LeftFractionColimit
public import ReasLib.CategoryTheory.MorphismProperty.Localization.RightFractionColimit

/-!
# Derived definedness on denominator categories

The comma-category diagrams in the canonical definitions of pointwise derived functors can be
tested on ordinary target or source denominators.  This file owns those smaller diagrams and the
Prop-valued comparison API.  Concrete comparisons of their (co)limits with pointwise derived
values live in `PointwiseValue/Denominator`.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace RightDerived.Denominator

/-- The target-denominator diagram which computes the pointwise right-derived value at `X`. -/
@[stacks 05T5 "target-denominator diagram for a pointwise right-derived value"]
noncomputable abbrev diagram (F : C ⥤ D) (S : MorphismProperty C) (X : C) :
    MorphismProperty.Under S ⊤ X ⥤ D :=
  MorphismProperty.Under.toCostructuredArrow S X ⋙
    CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F

/-- The target-denominator diagram evaluates a denominator at its target. -/
@[simp]
theorem diagram_obj (F : C ⥤ D) (S : MorphismProperty C) (X : C)
    (U : MorphismProperty.Under S ⊤ X) :
    (diagram F S X).obj U = F.obj U.right := sorry

/-- The target-denominator diagram acts on a refinement through its target map. -/
@[simp]
theorem diagram_map (F : C ⥤ D) (S : MorphismProperty C) (X : C)
    {U V : MorphismProperty.Under S ⊤ X} (f : U ⟶ V) :
    (diagram F S X).map f = F.map f.right := sorry

end RightDerived.Denominator

namespace LeftDerived.Denominator

/-- The source-denominator diagram which computes the pointwise left-derived value at `X`. -/
@[stacks 05T5 "source-denominator diagram for a pointwise left-derived value"]
noncomputable abbrev diagram (F : C ⥤ D) (S : MorphismProperty C) (X : C) :
    MorphismProperty.Over S ⊤ X ⥤ D :=
  MorphismProperty.Over.toStructuredArrow S X ⋙
    StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F

/-- The source-denominator diagram evaluates a denominator at its source. -/
@[simp]
theorem diagram_obj (F : C ⥤ D) (S : MorphismProperty C) (X : C)
    (U : MorphismProperty.Over S ⊤ X) :
    (diagram F S X).obj U = F.obj U.left := sorry

/-- The source-denominator diagram acts on a refinement through its source map. -/
@[simp]
theorem diagram_map (F : C ⥤ D) (S : MorphismProperty C) (X : C)
    {U V : MorphismProperty.Over S ⊤ X} (f : U ⟶ V) :
    (diagram F S X).map f = F.map f.left := sorry

end LeftDerived.Denominator

/-- Source-definedness of a pointwise right-derived value is detected on the ordinary
target-denominator diagram. -/
@[stacks 05T5 "right-derived definedness on target denominators"]
theorem RightDerived.DefinedAt.iff_denominator (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) :
    RightDerived.DefinedAt F S X ↔
      IsFiltered.IsEssentiallyConstant (RightDerived.Denominator.diagram F S X) := sorry

/-- Source-definedness supplies essential constancy of the target-denominator diagram. -/
theorem RightDerived.DefinedAt.denominator_isEssentiallyConstant
    (F : C ⥤ D) (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    (X : C) [RightDerived.DefinedAt F S X] :
    IsFiltered.IsEssentiallyConstant (RightDerived.Denominator.diagram F S X) := sorry

/-- Source-definedness of a pointwise left-derived value is detected on the ordinary
source-denominator diagram. -/
@[stacks 05T5 "left-derived definedness on source denominators"]
theorem LeftDerived.DefinedAt.iff_denominator (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) :
    LeftDerived.DefinedAt F S X ↔
      IsCofiltered.IsEssentiallyConstant (LeftDerived.Denominator.diagram F S X) := sorry

/-- Source-definedness supplies essential constancy of the source-denominator diagram. -/
theorem LeftDerived.DefinedAt.denominator_isEssentiallyConstant
    (F : C ⥤ D) (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    (X : C) [LeftDerived.DefinedAt F S X] :
    IsCofiltered.IsEssentiallyConstant (LeftDerived.Denominator.diagram F S X) := sorry

/-- Mathlib's pointwise right-derived existence predicate is equivalent to existence of the
target-denominator colimit. -/
theorem RightDerived.hasPointwiseAt_iff_denominator
    (F : C ⥤ D) (S : MorphismProperty C) [S.HasLeftCalculusOfFractions] (X : C) :
    F.HasPointwiseRightDerivedFunctorAt S X ↔
      HasColimit (RightDerived.Denominator.diagram F S X) := sorry

/-- A source-defined right-derived value canonically supplies the target-denominator colimit. -/
noncomputable instance RightDerived.DefinedAt.denominatorHasColimit
    (F : C ⥤ D) (S : MorphismProperty C) [S.HasLeftCalculusOfFractions]
    (X : C) [RightDerived.DefinedAt F S X] :
    HasColimit (RightDerived.Denominator.diagram F S X) := sorry

/-- Mathlib's pointwise left-derived existence predicate is equivalent to existence of the
source-denominator limit. -/
theorem LeftDerived.hasPointwiseAt_iff_denominator
    (F : C ⥤ D) (S : MorphismProperty C) [S.HasRightCalculusOfFractions] (X : C) :
    F.HasPointwiseLeftDerivedFunctorAt S X ↔
      HasLimit (LeftDerived.Denominator.diagram F S X) := sorry

/-- A source-defined left-derived value canonically supplies the source-denominator limit. -/
noncomputable instance LeftDerived.DefinedAt.denominatorHasLimit
    (F : C ⥤ D) (S : MorphismProperty C) [S.HasRightCalculusOfFractions]
    (X : C) [LeftDerived.DefinedAt F S X] :
    HasLimit (LeftDerived.Denominator.diagram F S X) := sorry




end CategoryTheory.Functor
