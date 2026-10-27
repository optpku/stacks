/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded.K0
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.CohomologyIn
public import ReasLib.CategoryTheory.Pretriangulated.K0.Euler
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Grothendieck Groups of Bounded Cohomology-In Subcategories

For a weak Serre object property `P`, the degree-zero embedding and the
cohomological Euler characteristic identify `AbelianK0 P.FullSubcategory`
with the triangulated Grothendieck group of
`DerivedCategory.Bounded.CohomologyIn P`.
-/

open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated
open scoped BigOperators

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]
variable (P : ObjectProperty A) [IsWeakSerreClass P]

set_option backward.isDefEq.respectTransparency false in
/-- Short-exact relations in `P.FullSubcategory` are killed by the
degree-zero embedding. -/
theorem relations_le_ker_fromAbelian :
    AbelianK0.relations P.FullSubcategory ≤
      (FreeAbelianGroup.lift fun X : P.FullSubcategory ↦
        TriangulatedK0.of ((Single.functor P).obj X)).ker := by
  classical
  refine (AddSubgroup.closure_le _).mpr ?_
  rintro _ ⟨⟨S, hS⟩, rfl⟩
  let hS' := hS.map_of_exact P.ι
  let T : Triangle (DerivedCategory.Bounded.CohomologyIn P) :=
    Triangle.mk ((Single.functor P).map S.f) ((Single.functor P).map S.g)
      (ObjectProperty.homMk (ObjectProperty.homMk
        (hS'.singleδ ≫ ((ambient P).commShiftIso (1 : ℤ)).inv.app
          ((Single.functor P).obj S.X₁))))
  have hT : T ∈ distTriang (DerivedCategory.Bounded.CohomologyIn P) := by
    apply ((ambient P).map_distinguished_iff T).mp
    dsimp only [T, Functor.mapTriangle, Triangle.mk]
    change Triangle.mk _ _ ((hS'.singleδ ≫
      ((ambient P).commShiftIso (1 : ℤ)).inv.app ((Single.functor P).obj S.X₁)) ≫
      ((ambient P).commShiftIso (1 : ℤ)).hom.app ((Single.functor P).obj S.X₁)) ∈ _
    rw [Category.assoc, Iso.inv_hom_id_app]
    change Triangle.mk ((DerivedCategory.singleFunctor A 0).map S.f.hom)
      ((DerivedCategory.singleFunctor A 0).map S.g.hom) (hS'.singleδ ≫ 𝟙 _) ∈ _
    rw [Category.comp_id]
    exact hS'.singleTriangle_distinguished
  have hrel : TriangulatedK0.relation (DerivedCategory.Bounded.CohomologyIn P) T ∈
      TriangulatedK0.relations (DerivedCategory.Bounded.CohomologyIn P) :=
    AddSubgroup.subset_closure ⟨⟨T, hT⟩, rfl⟩
  have hz : (QuotientAddGroup.mk'
      (TriangulatedK0.relations (DerivedCategory.Bounded.CohomologyIn P)))
      (TriangulatedK0.relation (DerivedCategory.Bounded.CohomologyIn P) T) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr hrel
  change FreeAbelianGroup.lift _ (AbelianK0.relation P.FullSubcategory ⟨S, hS⟩) = 0
  simpa only [AbelianK0.relation, TriangulatedK0.relation, T, Triangle.mk, map_sub,
    FreeAbelianGroup.lift_apply_of] using hz

/-- The degree-zero embedding induces a homomorphism from abelian `K₀` to
the triangulated `K₀` of bounded objects with cohomology in `P`. -/
@[stacks 0FCS]
noncomputable def fromAbelian :
    AbelianK0 P.FullSubcategory →+
      TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) :=
  AbelianK0.lift
    (fun X : P.FullSubcategory ↦ TriangulatedK0.of ((Single.functor P).obj X))
    (relations_le_ker_fromAbelian P)

/-- The degree-zero map sends an object class to the class of its lifted
degree-zero derived object. -/
@[stacks 0FCS, simp]
theorem fromAbelian_of (X : P.FullSubcategory) :
    fromAbelian P (AbelianK0.of X) =
      TriangulatedK0.of ((Single.functor P).obj X) := by
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of X) = _
  exact FreeAbelianGroup.lift_apply_of _ X

namespace Euler

/-- The Euler class of a bounded object with cohomology in `P`, expressed as
the finite alternating sum of its lifted cohomology objects. -/
@[stacks 0FCS]
noncomputable def value (X : DerivedCategory.Bounded.CohomologyIn P) :
    AbelianK0 P.FullSubcategory :=
  ∑ᶠ i : ℤ, i.negOnePow • AbelianK0.of ((Homology.functor P i).obj X)

end Euler

/-- The cohomological Euler characteristic from triangulated `K₀` to the
abelian `K₀` of `P.FullSubcategory`. -/
@[stacks 0FCS]
noncomputable def toAbelian :
    TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) →+
      AbelianK0 P.FullSubcategory :=
  (Homology.functor P 0).eulerK0Map (Homology.hasFiniteSupport P)

/-- The Euler homomorphism evaluates on an object class as the alternating
sum of its lifted cohomology classes. -/
@[stacks 0FCS, simp]
theorem toAbelian_of (X : DerivedCategory.Bounded.CohomologyIn P) :
    toAbelian P (TriangulatedK0.of X) = Euler.value P X := by
  change FreeAbelianGroup.lift _ (FreeAbelianGroup.of X) = _
  rw [FreeAbelianGroup.lift_apply_of]
  apply finsum_congr
  intro i
  congr 1
  apply AbelianK0.of_iso
  apply P.isoMk
  exact (DerivedCategory.homologyFunctor A 0).mapIso
      (((ambient P).commShiftIso i).app X) ≪≫
    ((DerivedCategory.homologyFunctor A 0).shiftIso i 0 i (add_zero i)).app X.obj.obj

/-- Euler characteristic after the degree-zero embedding is the identity
homomorphism. -/
@[stacks 0FCS]
theorem to_from :
    (toAbelian P).comp (fromAbelian P) =
      AddMonoidHom.id (AbelianK0 P.FullSubcategory) := by
  apply QuotientAddGroup.addMonoidHom_ext
  apply FreeAbelianGroup.lift_ext
  intro X
  change toAbelian P (fromAbelian P (AbelianK0.of X)) = AbelianK0.of X
  rw [fromAbelian_of, toAbelian_of]
  change (∑ᶠ i : ℤ, i.negOnePow •
    AbelianK0.of ((Homology.functor P i).obj ((Single.functor P).obj X))) = _
  rw [finsum_eq_single _ (0 : ℤ)]
  · simpa using AbelianK0.of_iso
      (P.isoMk ((DerivedCategory.Bounded.singleFunctor.compHomologyIso A 0).app X.obj))
  · intro i hi
    have hz : IsZero ((Homology.functor P i).obj ((Single.functor P).obj X)) := by
      apply IsZero.of_full_of_faithful_of_isZero P.ι
      exact DerivedCategory.Bounded.singleFunctor.isZero_homology_of_ne A 0 X.obj i hi
    rw [AbelianK0.of_iso (hz.iso (isZero_zero _)), AbelianK0.of_zero, smul_zero]

/-- Pointwise computation of Euler characteristic after the degree-zero
embedding. -/
@[simp]
theorem to_from_apply (x : AbelianK0 P.FullSubcategory) :
    toAbelian P (fromAbelian P x) = x := by
  exact DFunLike.congr_fun (to_from P) x

/-- The degree-zero embedding after Euler characteristic is the identity
homomorphism. -/
@[stacks 0FCS]
theorem from_to :
    (fromAbelian P).comp (toAbelian P) =
      AddMonoidHom.id
        (TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P)) := sorry

/-- Pointwise computation of the degree-zero embedding after Euler
characteristic. -/
@[simp]
theorem from_to_apply
    (x : TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P)) :
    fromAbelian P (toAbelian P x) = x := by
  exact DFunLike.congr_fun (from_to P) x

/-- The canonical additive equivalence between the abelian Grothendieck group of a weak Serre
class and the triangulated Grothendieck group of bounded derived objects whose cohomology lies
in that class. -/
@[stacks 0FCS]
noncomputable def equiv :
    AbelianK0 P.FullSubcategory ≃+
      TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) where
  toFun := fromAbelian P
  invFun := toAbelian P
  left_inv := DFunLike.congr_fun (to_from P)
  right_inv := DFunLike.congr_fun (from_to P)
  map_add' := (fromAbelian P).map_add

/-- The canonical additive equivalence from the bounded derived category of a weak Serre
subcategory to the bounded ambient derived objects whose cohomology lies in that subcategory. -/
@[stacks 0FDF]
noncomputable def comparisonEquiv [HasDerivedCategory.{w} P.FullSubcategory] :
    TriangulatedK0 (DerivedCategory.Bounded P.FullSubcategory) ≃+
      TriangulatedK0 (DerivedCategory.Bounded.CohomologyIn P) :=
  (DerivedCategory.Bounded.K0.equiv P.FullSubcategory).symm.trans (equiv P)

/-- The canonical equivalence sends an object class to its degree-zero
derived class. -/
@[stacks 0FCS, simp]
theorem equiv_apply_of (X : P.FullSubcategory) :
    equiv P (AbelianK0.of X) =
      TriangulatedK0.of ((Single.functor P).obj X) := by
  exact fromAbelian_of P X

/-- The inverse canonical equivalence sends a derived object class to its
cohomological Euler class. -/
@[stacks 0FCS, simp]
theorem equiv_symm_apply_of
    (X : DerivedCategory.Bounded.CohomologyIn P) :
    (equiv P).symm (TriangulatedK0.of X) = Euler.value P X := by
  exact toAbelian_of P X

end CategoryTheory.DerivedCategory.Bounded.CohomologyIn.K0
