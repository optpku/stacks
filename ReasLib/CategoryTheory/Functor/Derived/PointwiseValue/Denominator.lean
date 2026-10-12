/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Denominator
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Right

/-!
# Pointwise derived values on denominator categories

Under a calculus of fractions, the canonical pointwise derived value can be computed on the
ordinary denominator category.  The comparison is the standard final or initial reindexing
isomorphism; no representative or universal cone is chosen here.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open Limits

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]

namespace RightDerived.Value

/-- The colimit over target denominators is canonically isomorphic to the pointwise
right-derived value. -/
@[stacks 05T5 "pointwise right-derived value on target denominators"]
noncomputable def denominatorIso (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) [RightDerived.DefinedAt F S X] :
    colimit (RightDerived.Denominator.diagram F S X) ≅ obj F S X :=
  Functor.Final.colimitIso (MorphismProperty.Under.toCostructuredArrow S X)
    (CostructuredArrow.proj S.Q (S.Q.obj X) ⋙ F)

/-- The forward denominator comparison sends each target-denominator coprojection to the
canonical pointwise right-derived leg. -/
@[reassoc]
theorem denominatorIso_hom_ι (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) [RightDerived.DefinedAt F S X]
    (U : MorphismProperty.Under S ⊤ X) :
    colimit.ι (RightDerived.Denominator.diagram F S X) U ≫
        (denominatorIso F S X).hom =
      ι (X := X) F S U.hom U.prop := sorry

/-- The inverse denominator comparison sends the canonical pointwise right-derived leg back to
the target-denominator coprojection. -/
@[reassoc]
theorem denominatorIso_inv_ι (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) [RightDerived.DefinedAt F S X]
    (U : MorphismProperty.Under S ⊤ X) :
    ι (X := X) F S U.hom U.prop ≫ (denominatorIso F S X).inv =
      colimit.ι (RightDerived.Denominator.diagram F S X) U := sorry

/-- The denominator comparison at an ordinary target denominator, without exposing the
corresponding object of the denominator category. -/
@[reassoc]
theorem denominatorIso_hom_leg (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) [RightDerived.DefinedAt F S X]
    {Y : C} (s : X ⟶ Y) (hs : S s) :
    colimit.ι (RightDerived.Denominator.diagram F S X)
          (MorphismProperty.Under.mk ⊤ s hs) ≫
        (denominatorIso F S X).hom = ι F S s hs := sorry

/-- The inverse denominator comparison at an ordinary target denominator. -/
@[reassoc]
theorem denominatorIso_inv_leg (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasLeftCalculusOfFractions] (X : C) [RightDerived.DefinedAt F S X]
    {Y : C} (s : X ⟶ Y) (hs : S s) :
    ι F S s hs ≫ (denominatorIso F S X).inv =
      colimit.ι (RightDerived.Denominator.diagram F S X)
        (MorphismProperty.Under.mk ⊤ s hs) := sorry

end RightDerived.Value

namespace LeftDerived.Value

/-- The limit over source denominators is canonically isomorphic to the pointwise left-derived
value. -/
@[stacks 05T5 "pointwise left-derived value on source denominators"]
noncomputable def denominatorIso (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) [LeftDerived.DefinedAt F S X] :
    limit (LeftDerived.Denominator.diagram F S X) ≅ obj F S X :=
  Functor.Initial.limitIso (MorphismProperty.Over.toStructuredArrow S X)
    (StructuredArrow.proj (S.Q.obj X) S.Q ⋙ F)

/-- The forward denominator comparison intertwines the canonical source-denominator projection
with the pointwise left-derived projection. -/
@[reassoc]
theorem denominatorIso_hom_π (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) [LeftDerived.DefinedAt F S X]
    (U : MorphismProperty.Over S ⊤ X) :
    (denominatorIso F S X).hom ≫ π (X := X) F S U.hom U.prop =
      limit.π (LeftDerived.Denominator.diagram F S X) U := sorry

/-- The inverse denominator comparison identifies the source-denominator projection with the
canonical pointwise left-derived projection. -/
@[reassoc]
theorem denominatorIso_inv_π (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) [LeftDerived.DefinedAt F S X]
    (U : MorphismProperty.Over S ⊤ X) :
    (denominatorIso F S X).inv ≫
        limit.π (LeftDerived.Denominator.diagram F S X) U =
      π (X := X) F S U.hom U.prop := sorry

/-- The denominator comparison at an ordinary source denominator, without exposing the
corresponding object of the denominator category. -/
@[reassoc]
theorem denominatorIso_hom_leg (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) [LeftDerived.DefinedAt F S X]
    {Y : C} (s : Y ⟶ X) (hs : S s) :
    (denominatorIso F S X).hom ≫ π F S s hs =
      limit.π (LeftDerived.Denominator.diagram F S X)
        (MorphismProperty.Over.mk ⊤ s hs) := sorry

/-- The inverse denominator comparison at an ordinary source denominator. -/
@[reassoc]
theorem denominatorIso_inv_leg (F : C ⥤ D) (S : MorphismProperty C)
    [S.HasRightCalculusOfFractions] (X : C) [LeftDerived.DefinedAt F S X]
    {Y : C} (s : Y ⟶ X) (hs : S s) :
    (denominatorIso F S X).inv ≫
        limit.π (LeftDerived.Denominator.diagram F S X)
          (MorphismProperty.Over.mk ⊤ s hs) = π F S s hs := sorry

end LeftDerived.Value




end CategoryTheory.Functor
