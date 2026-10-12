/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal
public import ReasLib.CategoryTheory.Homology.DoubleComplex.TotalComparison

/-!
# Additive-Functor/Total Comparisons on the Coordinate Axes

The additive-functor comparison for total complexes is compatible with the canonical maps from
the zeroth row and zeroth column.  These equalities are the bridge used when a resolution
augmentation is totalized before or after applying a functor.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace HomologicalComplex₂

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D] [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]
variable {K : CochainComplex C ℤ} {A : HomologicalComplex₂ C (up ℤ) (up ℤ)}
variable [A.HasTotal (up ℤ)]
variable [((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj A).HasTotal (up ℤ)]

namespace ZeroRow

namespace ToTotal

namespace Map

/-- Applying an additive functor to a zeroth-row map preserves its vertical-cycle condition. -/
@[stacks 0132 "mapped zeroth-row cycle condition"]
theorem cycles (f : K ⟶ A.zeroRow)
    (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) :
    ∀ p : ℤ,
      ((F.mapHomologicalComplex (up ℤ)).map f).f p ≫
        (((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj A).X p).d 0 1 = 0 := sorry

/-- The zeroth-row comparison obtained after applying an additive functor agrees, after the
canonical total comparison, with the image of the original zeroth-row comparison. -/
@[stacks 0132 "mapped zeroth-row total comparison", reassoc]
theorem comparison
    (f : K ⟶ A.zeroRow) (hf : ∀ p : ℤ, f.f p ≫ (A.X p).d 0 1 = 0) :
    ZeroRow.ToTotal.map ((F.mapHomologicalComplex (up ℤ)).map f)
          (cycles F f hf) ≫
        Total.Map.Comparison.hom F A (up ℤ) =
      (F.mapHomologicalComplex (up ℤ)).map (ZeroRow.ToTotal.map f hf) := sorry

end Map

end ToTotal

end ZeroRow

namespace ZeroColumn

namespace ToTotal

namespace Map

/-- Applying an additive functor to a zeroth-column map preserves its horizontal-cycle
condition. -/
@[stacks 0132 "mapped zeroth-column cycle condition"]
theorem cycles (f : K ⟶ A.zeroColumn)
    (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    ∀ q : ℤ,
      ((F.mapHomologicalComplex (up ℤ)).map f).f q ≫
        (((F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj A).d 0 1).f q = 0 := sorry

/-- The zeroth-column comparison obtained after applying an additive functor agrees, after the
canonical total comparison, with the image of the original zeroth-column comparison. -/
@[stacks 0132 "mapped zeroth-column total comparison", reassoc]
theorem comparison
    (f : K ⟶ A.zeroColumn) (hf : ∀ q : ℤ, f.f q ≫ (A.d 0 1).f q = 0) :
    ZeroColumn.ToTotal.map ((F.mapHomologicalComplex (up ℤ)).map f)
          (cycles F f hf) ≫
        Total.Map.Comparison.hom F A (up ℤ) =
      (F.mapHomologicalComplex (up ℤ)).map (ZeroColumn.ToTotal.map f hf) := sorry

end Map

end ToTotal

end ZeroColumn

end HomologicalComplex₂
