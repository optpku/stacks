/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Data.Int.Interval
public import ReasLib.CategoryTheory.Filtration.Finite
import Mathlib.Tactic.CrossRefAttribute

/-!
# Interval-Split Filtered Objects

This module defines the finite filtered object obtained from a finite direct sum indexed by an
integer interval.  Its filtration at `p` is the direct sum of the summands whose indices are at
least `p`.  Computational lemmas for this construction live in `IntervalSplit.Computation`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
  [HasFiniteBiproducts C]
variable (a b : ℤ) (J : Set.Icc a b → C)

namespace IntervalTail

/-- The tail inclusion has the explicit complementary projection as its retraction. -/
def splitting (p : ℤ) :
    SplitMono (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1) where
  retraction := biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)
  id := biproduct.fromSubtype_toSubtype J _

/-- The canonical inclusion of the summands indexed by `i ≥ p` into the interval biproduct is a
split monomorphism. -/
instance splitMono (p : ℤ) :
    IsSplitMono (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1) where
  exists_splitMono := ⟨splitting a b J p⟩

/-- The subobject of an interval-indexed biproduct consisting of the summands whose index is at
least `p`. -/
@[reducible]
noncomputable def subobject (p : ℤ) : Subobject (⨁ J) :=
  Subobject.mk (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

/-- The carrier of an interval tail is canonically the biproduct indexed by the corresponding
subtype. -/
@[reducible]
noncomputable def isoBiproduct (p : ℤ) :
    (((subobject a b J p : Subobject (⨁ J)) : C)) ≅
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  Subobject.underlyingIso (biproduct.fromSubtype J fun i : Set.Icc a b ↦ p ≤ i.1)

namespace IsoBiproduct

/-- Under the tail-carrier identification, the subobject arrow is the canonical subtype
inclusion. -/
theorem hom_comp_fromSubtype (p : ℤ) :
    (isoBiproduct a b J p).hom ≫
        biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      (subobject a b J p).arrow :=
  @CategoryTheory.Subobject.underlyingIso_hom_comp_eq_mk C _ _ _
    (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1))
    (by infer_instance)

/-- Under the tail-carrier identification, its inverse followed by the tail arrow is the
canonical subtype inclusion. -/
theorem inv_comp_arrow (p : ℤ) :
    (isoBiproduct a b J p).inv ≫ (subobject a b J p).arrow =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) :=
  @CategoryTheory.Subobject.underlyingIso_arrow C _ _ _
    (biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1))
    (by infer_instance)

end IsoBiproduct

/-- The inclusion between two tail biproducts, given on each summand by the same interval
index. This is the witness for antitonicity of the tail subobjects. -/
def mapOfLE {p q : ℤ} (hpq : p ≤ q) :
    (⨁ fun i : { i : Set.Icc a b // q ≤ i.1 } ↦ J i.1) ⟶
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  biproduct.desc fun i : { i : Set.Icc a b // q ≤ i.1 } ↦
    biproduct.ι (fun j : { i : Set.Icc a b // p ≤ i.1 } ↦ J j.1)
      ⟨i.1, hpq.trans i.2⟩

/-- The explicit map of tails commutes with their inclusions into the full biproduct. -/
theorem mapOfLE_comp_fromSubtype {p q : ℤ} (hpq : p ≤ q) :
    mapOfLE a b J hpq ≫ biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1) =
      biproduct.fromSubtype J (fun i : Set.Icc a b ↦ q ≤ i.1) := by
  apply biproduct.hom_ext'
  intro i
  simp only [mapOfLE, biproduct.ι_desc_assoc]
  exact (biproduct.ι_fromSubtype J (fun j : Set.Icc a b ↦ p ≤ j.1)
    ⟨i.1, hpq.trans i.2⟩).trans
      (biproduct.ι_fromSubtype J (fun j : Set.Icc a b ↦ q ≤ j.1) i).symm

/-- Increasing the cutoff shrinks the corresponding interval-tail subobject. -/
theorem antitone {p q : ℤ} (hpq : p ≤ q) :
    subobject a b J q ≤ subobject a b J p :=
  Subobject.mk_le_mk_of_comm (mapOfLE a b J hpq) (mapOfLE_comp_fromSubtype a b J hpq)

/-- The canonical map from the `q`-tail to the `p`-tail when `p ≤ q`. -/
@[reducible]
noncomputable def ofLE {p q : ℤ} (hpq : p ≤ q) :
    (((subobject a b J q : Subobject (⨁ J)) : C)) ⟶
      (((subobject a b J p : Subobject (⨁ J)) : C)) :=
  Subobject.ofLE _ _ (antitone a b J hpq)

namespace OfLE

/-- The canonical map between interval tails commutes with their arrows into the ambient
biproduct. -/
theorem arrow {p q : ℤ} (hpq : p ≤ q) :
    ofLE a b J hpq ≫ (subobject a b J p).arrow =
      (subobject a b J q).arrow :=
  CategoryTheory.Subobject.ofLE_arrow _

end OfLE

namespace Filtration

/-- The interval-tail assignment is monotone when the integer index is viewed in the opposite
order. -/
theorem monotone :
    Monotone (fun p : ℤᵒᵈ ↦ subobject a b J p) :=
  fun _ _ hpq ↦ antitone a b J (OrderDual.toDual_le_toDual.mp hpq)

end Filtration

/-- The decreasing filtration on the interval biproduct whose stage at `p` is the tail over
indices `q ≥ p`. -/
noncomputable def filtration : DecreasingFiltration (⨁ J) where
  toFun := fun p ↦ subobject a b J p
  monotone' := Filtration.monotone a b J

namespace Subobject

/-- A tail stage weakly to the left of the interval is the whole interval biproduct. -/
theorem eq_top_of_le_left {p : ℤ} (hp : p ≤ a) :
    subobject a b J p = ⊤ := by
  classical
  let e : (⨁ fun i : {i : Set.Icc a b // p ≤ i.1} ↦ J i.1) ≅ (⨁ J) :=
    { hom := biproduct.fromSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)
      inv := biproduct.toSubtype J (fun i : Set.Icc a b ↦ p ≤ i.1)
      hom_inv_id := biproduct.fromSubtype_toSubtype J _
      inv_hom_id := by
        apply biproduct.hom_ext'
        intro i
        erw [← Category.assoc, biproduct.ι_toSubtype, dif_pos (hp.trans i.2.1),
          biproduct.ι_fromSubtype, Category.comp_id] }
  letI := e.isIso_hom
  exact CategoryTheory.Subobject.mk_eq_top_of_isIso e.hom

/-- A tail stage strictly to the right of the interval is zero. -/
theorem eq_bot_of_right_lt {p : ℤ} (hp : b < p) :
    subobject a b J p = ⊥ := by
  apply CategoryTheory.Subobject.mk_eq_bot_iff_zero.mpr
  apply biproduct.hom_ext'
  intro i
  have hi := i.1.2.2
  have hip := i.2
  exact (False.elim (by omega : False))

end Subobject
end IntervalTail

namespace IntervalSplit

/-- The interval-tail filtration has a top and a zero stage. -/
theorem isFinite :
    FilteredObject.IsFinite
      ({ obj := ⨁ J
         filtration := IntervalTail.filtration a b J } : FilteredObject C) :=
  ⟨a, b + 1, IntervalTail.Subobject.eq_top_of_le_left a b J (p := a) le_rfl,
    IntervalTail.Subobject.eq_bot_of_right_lt a b J (p := b + 1) (by omega)⟩

/-- The finite filtered object formed from an interval-indexed family of summands, with the tail
filtration. -/
@[stacks 05TP "canonical interval-split filtered model"]
noncomputable def filteredObject : FilteredObject.Finite.category C :=
  ⟨{ obj := ⨁ J
     filtration := IntervalTail.filtration a b J },
    isFinite a b J⟩

/-- The `p`-th stage of an interval-split filtered object is its canonical `p`-tail subobject. -/
theorem filtration_obj (p : ℤ) :
    (filteredObject a b J).obj.filtration.stage p = IntervalTail.subobject a b J p := rfl

namespace Stage

/-- The `p`-th stage of an interval-split filtered object is canonically the corresponding
subtype biproduct. -/
@[reducible]
noncomputable def iso (p : ℤ) :
    (((filteredObject a b J).obj.filtration.stage p : Subobject _) : C) ≅
      (⨁ fun i : { i : Set.Icc a b // p ≤ i.1 } ↦ J i.1) :=
  IntervalTail.isoBiproduct a b J p

end Stage
end IntervalSplit

end CategoryTheory.FilteredObject
