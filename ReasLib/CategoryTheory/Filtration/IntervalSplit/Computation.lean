module

public import ReasLib.CategoryTheory.Filtration.IntervalSplit.Basic

/-!
# Computations for Interval-Split Filtered Objects

This module records the arrow and factorization formulas for the interval-tail filtration.  These
are the stable downstream interface for constructing filtered maps into interval-split objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasFiniteBiproducts C]
variable (a b : ℤ) (J : Set.Icc a b → C)

namespace IntervalSplit.Stage.Iso

/-- Under the canonical stage identification, the stage arrow of an interval-split filtered
object is the expected subtype inclusion. -/
theorem hom_comp_fromSubtype (p : ℤ) :
      (IntervalSplit.Stage.iso a b J p).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      ((IntervalSplit.filteredObject a b J).obj.filtration.stage p).arrow := sorry

/-- Under the canonical stage identification, its inverse followed by the stage arrow is the
expected subtype inclusion. -/
theorem inv_comp_arrow (p : ℤ) :
    (IntervalSplit.Stage.iso a b J p).inv ≫
        ((IntervalSplit.filteredObject a b J).obj.filtration.stage p).arrow =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) := sorry

end IntervalSplit.Stage.Iso

namespace IntervalTail.Subobject

/-- A map into an interval biproduct factors through the `p`-tail exactly when its components at
all excluded indices vanish. -/
theorem factors_iff_component_zero {p : ℤ} {W : C} (g : W ⟶ ⨁ J) :
    (IntervalTail.subobject a b J p).Factors g ↔
      ∀ i : Set.Icc a b, ¬ p ≤ i.1 → g ≫ biproduct.π J i = 0 := sorry

end IntervalTail.Subobject

namespace IntervalSplit.Stage

/-- A map into the ambient biproduct factors through the `p`-th stage of the interval-split
filtered object exactly when all components below `p` vanish. -/
theorem factors_iff_component_zero {p : ℤ} {W : C} (g : W ⟶ ⨁ J) :
    ((IntervalSplit.filteredObject a b J).obj.filtration.stage p).Factors g ↔
      ∀ i : Set.Icc a b, ¬ p ≤ i.1 → g ≫ biproduct.π J i = 0 := sorry

/-- The `p`-th stage arrow has zero component at every interval summand strictly below `p`. -/
theorem arrow_comp_π_eq_zero_of_not_le (p : ℤ) (i : Set.Icc a b) (hi : ¬ p ≤ i.1) :
    ((IntervalSplit.filteredObject a b J).obj.filtration.stage p).arrow ≫
      biproduct.π J i = 0 := sorry

end IntervalSplit.Stage

end CategoryTheory.FilteredObject
