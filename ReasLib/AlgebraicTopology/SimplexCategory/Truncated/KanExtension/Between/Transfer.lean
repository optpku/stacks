module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Between
public import ReasLib.CategoryTheory.Functor.LeftKanExtension.ColimitMap
public import ReasLib.CategoryTheory.Functor.RightKanExtension.LimitMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Transfer of Kan extensions between truncation levels

This leaf owns the indexing-category equivalences and pointwise Kan-extension transfer instances
from a full truncated-simplex inclusion to an intermediate inclusion.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u v

namespace SimplexCategory.Truncated

variable {C : Type u} [Category.{v} C]

namespace incl

/-- The structured-arrow category for `Δ≤n ⥤ Δ≤m` is canonically equivalent to the matching
category for `Δ≤n ⥤ Δ`. -/
@[stacks 018B "structured-arrow comparison between truncation levels"]
noncomputable def structuredArrowEquiv (n m : ℕ) (h : n ≤ m)
    (Y : (SimplexCategory.Truncated m)ᵒᵖ) :
    StructuredArrow Y (incl n m h).op ≌
      StructuredArrow ((inclusion m).op.obj Y) (inclusion n).op :=
  (StructuredArrow.post Y (incl n m h).op (inclusion m).op).asEquivalence.trans
    (StructuredArrow.mapNatIso
      ((Functor.opComp (incl n m h) (inclusion m)).symm ≪≫
        NatIso.op (inclCompInclusion h).symm))

/-- The costructured-arrow category for `Δ≤n ⥤ Δ≤m` is canonically equivalent to the skeleton
indexing category for `Δ≤n ⥤ Δ`. -/
@[stacks 018N "costructured-arrow comparison between truncation levels"]
noncomputable def costructuredArrowEquiv (n m : ℕ) (h : n ≤ m)
    (Y : (SimplexCategory.Truncated m)ᵒᵖ) :
    CostructuredArrow (incl n m h).op Y ≌
      CostructuredArrow (inclusion n).op ((inclusion m).op.obj Y) :=
  (CostructuredArrow.post (incl n m h).op (inclusion m).op Y).asEquivalence.trans
    (CostructuredArrow.mapNatIso
      ((Functor.opComp (incl n m h) (inclusion m)).symm ≪≫
        NatIso.op (inclCompInclusion h).symm))

namespace pointwise.right

/-- A pointwise right Kan extension along the full inclusion restricts to every larger
truncation level. -/
@[stacks 018B "pointwise right Kan extension between truncation levels"]
instance kanExtension
    (n m : ℕ) (h : n ≤ m) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C)
    [(inclusion n).op.HasPointwiseRightKanExtension F] :
    SimplicialObject.Truncated.Between.HasPointwiseCoskeleton F m h :=
  fun Y ↦ Limits.hasLimit_equivalence_comp
    (F := StructuredArrow.proj ((inclusion m).op.obj Y) (inclusion n).op ⋙ F)
    (structuredArrowEquiv n m h Y)

/-- Pointwise coskeletons along the full inclusion supply pointwise coskeletons between every
pair of truncation levels. -/
@[stacks 018B "pointwise coskeletons between truncation levels"]
instance kanExtensions
    (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseCoskeletons C n] :
    SimplicialObject.Truncated.Between.HasPointwiseCoskeletons C n m h :=
  fun _ ↦ inferInstance

end pointwise.right

namespace pointwise.left

/-- A pointwise left Kan extension along the full inclusion restricts to every larger truncation
level. -/
@[stacks 018N "pointwise left Kan extension between truncation levels"]
instance kanExtension
    (n m : ℕ) (h : n ≤ m) (F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C)
    [(inclusion n).op.HasPointwiseLeftKanExtension F] :
    SimplicialObject.Truncated.Between.HasPointwiseSkeleton F m h :=
  fun Y ↦ Limits.hasColimit_equivalence_comp
    (F := CostructuredArrow.proj (inclusion n).op ((inclusion m).op.obj Y) ⋙ F)
    (costructuredArrowEquiv n m h Y)

/-- Pointwise skeletons along the full inclusion supply pointwise skeletons between every pair
of truncation levels. -/
@[stacks 018N "pointwise skeletons between truncation levels"]
instance kanExtensions
    (n m : ℕ) (h : n ≤ m)
    [SimplicialObject.Truncated.HasPointwiseSkeletons C n] :
    SimplicialObject.Truncated.Between.HasPointwiseSkeletons C n m h :=
  fun _ ↦ inferInstance

end pointwise.left

end incl

end SimplexCategory.Truncated
