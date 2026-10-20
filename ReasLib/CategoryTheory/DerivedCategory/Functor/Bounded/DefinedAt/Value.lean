module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Indexing
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.DefinedAt.Instances
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.FullSubcategory.Comparison
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Left
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Right
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded and unbounded pointwise derived values

At an object where both bounded and unbounded indexing diagrams are essentially constant, their
pointwise derived values agree after applying the bounded derived inclusion.  The comparison is
built from final or initial reindexing and the explicit indexing-diagram isomorphism; it does not
require the stronger identity-denominator computation condition.
-/

@[expose] public section

open CategoryTheory ComplexShape CategoryTheory.Limits

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B]
  [Abelian A] [Abelian B] [HasDerivedCategory.{w} B]

namespace RightDerived.Value

/-- Stacks 05T5: the bounded-below and unbounded pointwise right-derived values agree whenever
both localization-indexed diagrams are essentially constant. -/
@[stacks 05T5 "bounded-below pointwise right-derived value comparison"]
noncomputable def boundedBelowIso (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A)
    [hK : RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    DerivedCategory.Plus.ι.obj
        (RightDerived.Value.obj F.toBoundedBelowDerived
          (HomotopyCategory.Plus.quasiIso A) K) ≅
      RightDerived.Value.obj (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) K.obj :=
  IsFiltered.IsEssentiallyConstant.FullSubcategory.colimitIsoOfFinal
    ((HomotopyCategory.Plus.Ambient.localizerMorphism A).costructuredArrow K)
    (boundedBelowDiagramIso F K)
    (ambientColimit := RightDerived.Value.hasColimit
      (Functor.Homotopy.toDerived F) (HomotopyCategory.quasiIso A (up ℤ)) K.obj)
    (inferInstance : RightDerived.DefinedAt F.toBoundedBelowDerived
      (HomotopyCategory.Plus.quasiIso A) K).isEssentiallyConstant

namespace boundedBelowIso

/-- The forward bounded-below value comparison identifies every bounded colimit leg with the
corresponding unbounded leg. -/
@[reassoc, stacks 05T5 "bounded-below value comparison on colimit legs"]
theorem hom_colimit_ι (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    (U : CostructuredArrow (HomotopyCategory.Plus.quasiIso A).Q
      ((HomotopyCategory.Plus.quasiIso A).Q.obj K)) :
    DerivedCategory.Plus.ι.map
          (colimit.ι
            (CostructuredArrow.proj (HomotopyCategory.Plus.quasiIso A).Q
              ((HomotopyCategory.Plus.quasiIso A).Q.obj K) ⋙
                F.toBoundedBelowDerived) U) ≫
        (boundedBelowIso F K).hom =
      colimit.ι
        (CostructuredArrow.proj (HomotopyCategory.quasiIso A (up ℤ)).Q
          ((HomotopyCategory.quasiIso A (up ℤ)).Q.obj K.obj) ⋙
            Functor.Homotopy.toDerived F)
        ((HomotopyCategory.Plus.Ambient.localizerMorphism A).costructuredArrow K |>.obj U) := sorry

/-- The inverse bounded-below value comparison identifies every unbounded colimit leg in the
image with the corresponding bounded leg. -/
@[reassoc, stacks 05T5 "bounded-below value comparison inverse on colimit legs"]
theorem colimit_ι_inv (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Plus A)
    [RightDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    (U : CostructuredArrow (HomotopyCategory.Plus.quasiIso A).Q
      ((HomotopyCategory.Plus.quasiIso A).Q.obj K)) :
    colimit.ι
          (CostructuredArrow.proj (HomotopyCategory.quasiIso A (up ℤ)).Q
            ((HomotopyCategory.quasiIso A (up ℤ)).Q.obj K.obj) ⋙
              Functor.Homotopy.toDerived F)
          ((HomotopyCategory.Plus.Ambient.localizerMorphism A).costructuredArrow K |>.obj U) ≫
        (boundedBelowIso F K).inv =
      DerivedCategory.Plus.ι.map
        (colimit.ι
          (CostructuredArrow.proj (HomotopyCategory.Plus.quasiIso A).Q
            ((HomotopyCategory.Plus.quasiIso A).Q.obj K) ⋙
              F.toBoundedBelowDerived) U) := sorry

end boundedBelowIso

end RightDerived.Value

namespace LeftDerived.Value

/-- Stacks 05T5: the bounded-above and unbounded pointwise left-derived values agree whenever
both localization-indexed diagrams are essentially constant. -/
@[stacks 05T5 "bounded-above pointwise left-derived value comparison"]
noncomputable def boundedAboveIso (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A)
    [hK : LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj] :
    DerivedCategory.Minus.ι.obj
        (LeftDerived.Value.obj F.toBoundedAboveDerived
          (HomotopyCategory.Minus.quasiIso A) K) ≅
      LeftDerived.Value.obj (Functor.Homotopy.toDerived F)
        (HomotopyCategory.quasiIso A (up ℤ)) K.obj :=
  IsCofiltered.IsEssentiallyConstant.FullSubcategory.limitIsoOfInitial
    ((HomotopyCategory.Minus.Ambient.localizerMorphism A).structuredArrow K)
    (boundedAboveDiagramIso F K)
    (ambientLimit := LeftDerived.Value.hasLimit
      (Functor.Homotopy.toDerived F) (HomotopyCategory.quasiIso A (up ℤ)) K.obj)
    (inferInstance : LeftDerived.DefinedAt F.toBoundedAboveDerived
      (HomotopyCategory.Minus.quasiIso A) K).isEssentiallyConstant

namespace boundedAboveIso

/-- The forward bounded-above value comparison identifies every unbounded limit projection in
the image with the corresponding bounded projection. -/
@[reassoc, stacks 05T5 "bounded-above value comparison on limit projections"]
theorem hom_limit_π (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    (U : StructuredArrow ((HomotopyCategory.Minus.quasiIso A).Q.obj K)
      (HomotopyCategory.Minus.quasiIso A).Q) :
    (boundedAboveIso F K).hom ≫
        limit.π
          (StructuredArrow.proj
            ((HomotopyCategory.quasiIso A (up ℤ)).Q.obj K.obj)
              (HomotopyCategory.quasiIso A (up ℤ)).Q ⋙
                Functor.Homotopy.toDerived F)
          ((HomotopyCategory.Minus.Ambient.localizerMorphism A).structuredArrow K |>.obj U) =
      DerivedCategory.Minus.ι.map
        (limit.π
          (StructuredArrow.proj ((HomotopyCategory.Minus.quasiIso A).Q.obj K)
            (HomotopyCategory.Minus.quasiIso A).Q ⋙ F.toBoundedAboveDerived) U) := sorry

/-- The inverse bounded-above value comparison identifies every bounded limit projection with
the corresponding unbounded projection. -/
@[reassoc, stacks 05T5 "bounded-above value comparison inverse on limit projections"]
theorem inv_limit_π (F : A ⥤ B) [F.Additive]
    (K : HomotopyCategory.Minus A)
    [LeftDerived.DefinedAt (Functor.Homotopy.toDerived F)
      (HomotopyCategory.quasiIso A (up ℤ)) K.obj]
    (U : StructuredArrow ((HomotopyCategory.Minus.quasiIso A).Q.obj K)
      (HomotopyCategory.Minus.quasiIso A).Q) :
    (boundedAboveIso F K).inv ≫
        DerivedCategory.Minus.ι.map
          (limit.π
            (StructuredArrow.proj ((HomotopyCategory.Minus.quasiIso A).Q.obj K)
              (HomotopyCategory.Minus.quasiIso A).Q ⋙ F.toBoundedAboveDerived) U) =
      limit.π
        (StructuredArrow.proj
          ((HomotopyCategory.quasiIso A (up ℤ)).Q.obj K.obj)
            (HomotopyCategory.quasiIso A (up ℤ)).Q ⋙
              Functor.Homotopy.toDerived F)
        ((HomotopyCategory.Minus.Ambient.localizerMorphism A).structuredArrow K |>.obj U) := sorry

end boundedAboveIso

end LeftDerived.Value



end CategoryTheory.Functor
