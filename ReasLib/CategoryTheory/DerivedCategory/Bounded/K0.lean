/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.SingleFunctor.Homology
public import ReasLib.CategoryTheory.Pretriangulated.K0.Euler
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The Grothendieck Group of a Bounded Derived Category

The degree-zero embedding and the cohomological Euler characteristic give inverse maps between
the abelian Grothendieck group of `A` and the triangulated Grothendieck group of
`DerivedCategory.Bounded A`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Pretriangulated
open scoped BigOperators

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Bounded.K0

variable (A : Type u) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Short-exact relations are killed by sending an abelian object to its degree-zero bounded
derived object. -/
theorem relations_le_ker_fromAbelian :
    AbelianK0.relations A ≤
      (FreeAbelianGroup.lift fun X : A ↦
        TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X)).ker := by
  apply (AddSubgroup.closure_le _).2
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  let ι : DerivedCategory.Bounded A ⥤ DerivedCategory A := DerivedCategory.Bounded.ι
  let T : Triangle (DerivedCategory.Bounded A) :=
    Triangle.mk ((DerivedCategory.Bounded.singleFunctor A 0).map S.f)
      ((DerivedCategory.Bounded.singleFunctor A 0).map S.g)
      (ι.preimage (hS.singleδ ≫ (ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁)))
  have hT : T ∈ distTriang (DerivedCategory.Bounded A) := by
    change ι.mapTriangle.obj T ∈ distTriang (DerivedCategory A)
    dsimp [Functor.mapTriangle, T]
    erw [ι.map_preimage]
    change Triangle.mk ((DerivedCategory.singleFunctor A 0).map S.f)
      ((DerivedCategory.singleFunctor A 0).map S.g)
      ((hS.singleδ ≫ (ι.commShiftIso (1 : ℤ)).inv.app
        ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁)) ≫
        (ι.commShiftIso (1 : ℤ)).hom.app
          ((DerivedCategory.Bounded.singleFunctor A 0).obj S.X₁)) ∈ _
    erw [Category.assoc, (ι.commShiftIso (1 : ℤ)).inv_hom_id_app, Category.comp_id]
    exact hS.singleTriangle_distinguished
  have hrel : TriangulatedK0.relation (DerivedCategory.Bounded A) T ∈
      TriangulatedK0.relations (DerivedCategory.Bounded A) :=
    AddSubgroup.subset_closure ⟨⟨T, hT⟩, rfl⟩
  have hzero := (QuotientAddGroup.eq_zero_iff _).2 hrel
  change FreeAbelianGroup.lift _ (AbelianK0.relation A ⟨S, hS⟩) = 0
  simpa [AbelianK0.relation, TriangulatedK0.relation, TriangulatedK0.of, T] using hzero

/-- The homomorphism from abelian `K₀` to bounded-derived triangulated `K₀` induced by the
degree-zero embedding. -/
@[stacks 0FCP]
noncomputable def fromAbelian :
    AbelianK0 A →+ TriangulatedK0 (DerivedCategory.Bounded A) :=
  AbelianK0.lift
    (fun X : A ↦ TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X))
    (relations_le_ker_fromAbelian A)

/-- The degree-zero embedding sends an object class to the class of its degree-zero bounded
derived object. -/
@[simp, stacks 0FCP]
theorem fromAbelian_of (X : A) :
    fromAbelian A (AbelianK0.of X) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X) := by
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of X) = _
  exact FreeAbelianGroup.lift_apply_of _ _

namespace Euler

/-- Degree-zero cohomology on the bounded derived category has bounded shift support at every
object. -/
@[stacks 0FCP]
theorem hasFiniteSupport (X : DerivedCategory.Bounded A) :
    (DerivedCategory.Bounded.homologyFunctor A 0).shiftVanishingBounded X := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := (DerivedCategory.bounded_iff X.obj).mp X.property
  constructor
  · refine ⟨a - 1, fun i hi ↦ ?_⟩
    exact (ha i (by omega)).of_iso
      (((DerivedCategory.Bounded.homologyFunctor A 0).isoShift i).app X)
  · refine ⟨b + 1, fun i hi ↦ ?_⟩
    exact (hb i (by omega)).of_iso
      (((DerivedCategory.Bounded.homologyFunctor A 0).isoShift i).app X)

/-- The Euler class of a bounded derived object, expressed as the finite alternating sum of its
cohomology classes. -/
@[stacks 0FCP]
noncomputable def value (X : DerivedCategory.Bounded A) : AbelianK0 A :=
  ∑ᶠ i : ℤ, i.negOnePow •
    AbelianK0.of
      ((DerivedCategory.Bounded.homologyFunctor A i).obj X)

end Euler

/-- The Euler-characteristic homomorphism from bounded-derived triangulated `K₀` to abelian
`K₀`. -/
@[stacks 0FCP]
noncomputable def toAbelian :
    TriangulatedK0 (DerivedCategory.Bounded A) →+ AbelianK0 A :=
  (DerivedCategory.Bounded.homologyFunctor A 0).eulerK0Map
    (Euler.hasFiniteSupport A)

/-- The Euler-characteristic homomorphism sends an object class to its cohomological Euler
class. -/
@[simp, stacks 0FCP]
theorem toAbelian_of (X : DerivedCategory.Bounded A) :
    toAbelian A (TriangulatedK0.of X) = Euler.value A X := by
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of X) = _
  rw [FreeAbelianGroup.lift_apply_of]
  rfl

/-- Applying Euler characteristic after the degree-zero embedding is the identity on abelian
`K₀`. -/
@[stacks 0FCP]
theorem to_from :
    (toAbelian A).comp (fromAbelian A) = AddMonoidHom.id (AbelianK0 A) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro X
  change toAbelian A (fromAbelian A (AbelianK0.of X)) = AbelianK0.of X
  rw [fromAbelian_of, toAbelian_of]
  unfold Euler.value
  rw [finsum_eq_single _ 0]
  · simpa using AbelianK0.of_iso
      ((DerivedCategory.Bounded.singleFunctor.compHomologyIso A 0).app X)
  · intro i hi
    have hzero : IsZero
        ((DerivedCategory.Bounded.homologyFunctor A i).obj
          ((DerivedCategory.Bounded.singleFunctor A 0).obj X)) := by
      change IsZero ((DerivedCategory.homologyFunctor A i).obj
        ((DerivedCategory.singleFunctor A 0).obj X))
      rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    rw [AbelianK0.of_iso
      hzero.isoZero, AbelianK0.of_zero, smul_zero]

/-- Pointwise computation of Euler characteristic after the degree-zero
embedding. -/
@[simp]
theorem to_from_apply (x : AbelianK0 A) :
    toAbelian A (fromAbelian A x) = x :=
  DFunLike.congr_fun (to_from A) x

/-- Applying the degree-zero embedding after Euler characteristic is the identity on
bounded-derived triangulated `K₀`. -/
@[stacks 0FCP]
theorem from_to :
    (fromAbelian A).comp (toAbelian A) =
      AddMonoidHom.id (TriangulatedK0 (DerivedCategory.Bounded A)) := sorry

/-- Pointwise computation of the degree-zero embedding after Euler
characteristic. -/
@[simp]
theorem from_to_apply (x : TriangulatedK0 (DerivedCategory.Bounded A)) :
    fromAbelian A (toAbelian A x) = x :=
  DFunLike.congr_fun (from_to A) x

/-- The canonical additive equivalence between abelian `K₀` and the triangulated `K₀` of the
bounded derived category. -/
@[stacks 0FCP]
noncomputable def equiv :
    AbelianK0 A ≃+ TriangulatedK0 (DerivedCategory.Bounded A) where
  toFun := fromAbelian A
  invFun := toAbelian A
  left_inv := DFunLike.congr_fun (to_from A)
  right_inv := DFunLike.congr_fun (from_to A)
  map_add' := (fromAbelian A).map_add

/-- The canonical equivalence sends an abelian object class to its degree-zero bounded-derived
class. -/
@[simp, stacks 0FCP]
theorem equiv_apply_of (X : A) :
    equiv A (AbelianK0.of X) =
      TriangulatedK0.of ((DerivedCategory.Bounded.singleFunctor A 0).obj X) :=
  fromAbelian_of A X

/-- The inverse canonical equivalence sends a bounded-derived object class to its Euler class. -/
@[simp, stacks 0FCP]
theorem equiv_symm_apply_of (X : DerivedCategory.Bounded A) :
    (equiv A).symm (TriangulatedK0.of X) = Euler.value A X :=
  toAbelian_of A X

end CategoryTheory.DerivedCategory.Bounded.K0
