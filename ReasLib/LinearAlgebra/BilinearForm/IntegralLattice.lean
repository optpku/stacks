/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.Quotient.Basic

@[expose] public section

open LinearMap LinearMap.BilinForm

universe u

/-- A full finite free integral lattice with a saturated sublattice and a symmetric
positive-definite rational bilinear form integral on lattice elements. -/
structure IntegralLatticePair (V : Type u) [AddCommGroup V] [Module ℚ V] where
  form : LinearMap.BilinForm ℚ V
  lattice : Submodule ℤ V
  sublattice : Submodule ℤ V
  sublatticeLe : sublattice ≤ lattice
  latticeFinite : Module.Finite ℤ lattice
  latticeFree : Module.Free ℤ lattice
  spans : Submodule.span ℚ (lattice : Set V) = ⊤
  quotientTorsionFree :
    Module.IsTorsionFree ℤ (lattice ⧸ sublattice.comap lattice.subtype)
  symmetric : form.IsSymm
  positiveDefinite : ∀ x : V, x ≠ 0 → 0 < form x x
  integral : ∀ x ∈ lattice, ∀ y ∈ lattice, form x y ∈ (1 : Submodule ℤ ℚ)

namespace IntegralLatticePair

variable {V : Type u} [AddCommGroup V] [Module ℚ V]

/-- Replaces the distinguished sublattice by a contained sublattice with torsion-free quotient,
preserving the ambient lattice and its integral bilinear form. -/
def withSublattice (C : IntegralLatticePair V) (N : Submodule ℤ V)
    (h_le : N ≤ C.lattice)
    (h_torsionFree : Module.IsTorsionFree ℤ (C.lattice ⧸ N.comap C.lattice.subtype)) :
    IntegralLatticePair V :=
  { C with
    sublattice := N
    sublatticeLe := h_le
    quotientTorsionFree := h_torsionFree }

/-- The sublattice replacement preserves the ambient lattice and form and uses the given
sublattice. -/
theorem withSublattice_spec (C : IntegralLatticePair V) (N : Submodule ℤ V)
    (h_le : N ≤ C.lattice)
    (h_torsionFree : Module.IsTorsionFree ℤ (C.lattice ⧸ N.comap C.lattice.subtype)) :
    ((C.withSublattice N h_le h_torsionFree).lattice,
        (C.withSublattice N h_le h_torsionFree).form) = (C.lattice, C.form) ∧
      (C.withSublattice N h_le h_torsionFree).sublattice = N := sorry

/-- The rational subspace spanned by an integral submodule. -/
def rationalSpan (N : Submodule ℤ V) : Submodule ℚ V :=
  Submodule.span ℚ (N : Set V)

/-- The integral dual of a submodule within its rational span, with respect to the pairing. -/
def dual (C : IntegralLatticePair V) (N : Submodule ℤ V) : Submodule ℤ V :=
  (rationalSpan N).restrictScalars ℤ ⊓ dualSubmodule C.form.flip N

/-- An element belongs to the integral dual exactly when it lies in the rational span
and pairs integrally with every element of the submodule. -/
theorem mem_dual_iff (C : IntegralLatticePair V) (N : Submodule ℤ V) (x : V) :
    x ∈ C.dual N ↔ x ∈ rationalSpan N ∧
      ∀ y ∈ N, C.form y x ∈ (1 : Submodule ℤ ℚ) := sorry

/-- The integral lattice orthogonal to the distinguished sublattice. -/
def orthogonal (C : IntegralLatticePair V) : Submodule ℤ V :=
  C.lattice ⊓
    (C.form.orthogonal (rationalSpan C.sublattice)).restrictScalars ℤ

/-- An element belongs to the orthogonal lattice exactly when it belongs to the
ambient lattice and pairs to zero with every element of the distinguished sublattice. -/
theorem mem_orthogonal_iff (C : IntegralLatticePair V) (x : V) :
    x ∈ C.orthogonal ↔ x ∈ C.lattice ∧
      ∀ a ∈ C.sublattice, C.form a x = 0 := sorry

/-- The rational span of the distinguished sublattice and its orthogonal subspace
are complementary. -/
theorem isCompl_rationalSpan_orthogonal (C : IntegralLatticePair V) :
    IsCompl (rationalSpan C.sublattice)
      (C.form.orthogonal (rationalSpan C.sublattice)) := sorry

/-- The rational orthogonal projection onto the span of the distinguished sublattice. -/
noncomputable def toSublatticeSpan (C : IntegralLatticePair V) : V →ₗ[ℚ] V :=
  @dite (V →ₗ[ℚ] V)
    (IsCompl (rationalSpan C.sublattice)
      (C.form.orthogonal (rationalSpan C.sublattice)))
    (Classical.propDecidable _)
    (fun h ↦ (rationalSpan C.sublattice).subtype.comp
      ((rationalSpan C.sublattice).projectionOnto
        (C.form.orthogonal (rationalSpan C.sublattice)) h))
    (fun _ ↦ 0)

/-- The sublattice projection takes values in the rational span of the sublattice. -/
theorem toSublatticeSpan_mem (C : IntegralLatticePair V) (x : V) :
    C.toSublatticeSpan x ∈ rationalSpan C.sublattice := sorry

/-- The rational orthogonal projection onto the orthogonal subspace of the sublattice. -/
noncomputable def toOrthogonalSpan (C : IntegralLatticePair V) : V →ₗ[ℚ] V :=
  @dite (V →ₗ[ℚ] V)
    (IsCompl (rationalSpan C.sublattice)
      (C.form.orthogonal (rationalSpan C.sublattice)))
    (Classical.propDecidable _)
    (fun h ↦ (C.form.orthogonal (rationalSpan C.sublattice)).subtype.comp
      ((C.form.orthogonal (rationalSpan C.sublattice)).projectionOnto
        (rationalSpan C.sublattice) h.symm))
    (fun _ ↦ 0)

/-- The orthogonal projection takes values in the rational span of the orthogonal lattice. -/
theorem toOrthogonalSpan_mem (C : IntegralLatticePair V) (x : V) :
    C.toOrthogonalSpan x ∈ rationalSpan C.orthogonal := sorry

/-- Projection of an ambient lattice element onto the sublattice span belongs to
the integral dual of the sublattice. -/
theorem toSublatticeSpan_mem_dual (C : IntegralLatticePair V) (x : C.lattice) :
    C.toSublatticeSpan x ∈ C.dual C.sublattice := sorry

/-- Projection of an ambient lattice element onto the orthogonal subspace belongs
to the integral dual of the orthogonal lattice. -/
theorem toOrthogonalSpan_mem_dual (C : IntegralLatticePair V) (x : C.lattice) :
    C.toOrthogonalSpan x ∈ C.dual C.orthogonal := sorry

/-- The integral linear map from the ambient lattice into the sublattice dual
induced by rational orthogonal projection. -/
noncomputable def leftLift (C : IntegralLatticePair V) :
    C.lattice →ₗ[ℤ] C.dual C.sublattice :=
  (((C.toSublatticeSpan.restrictScalars ℤ).domRestrict C.lattice).codRestrict
    (C.dual C.sublattice) C.toSublatticeSpan_mem_dual)

/-- The lift into the sublattice dual agrees with the rational sublattice projection. -/
theorem leftLift_apply (C : IntegralLatticePair V) (x : C.lattice) :
    C.leftLift x = C.toSublatticeSpan x := sorry

/-- The integral linear map from the ambient lattice into the orthogonal lattice dual
induced by rational orthogonal projection. -/
noncomputable def rightLift (C : IntegralLatticePair V) :
    C.lattice →ₗ[ℤ] C.dual C.orthogonal :=
  (((C.toOrthogonalSpan.restrictScalars ℤ).domRestrict C.lattice).codRestrict
    (C.dual C.orthogonal) C.toOrthogonalSpan_mem_dual)

/-- The lift into the orthogonal lattice dual agrees with the rational orthogonal projection. -/
theorem rightLift_apply (C : IntegralLatticePair V) (x : C.lattice) :
    C.rightLift x = C.toOrthogonalSpan x := sorry

/-- The submodule of an integral dual consisting of elements of the original submodule. -/
def insideDual (C : IntegralLatticePair V) (N : Submodule ℤ V) :
    Submodule ℤ (C.dual N) :=
  N.comap (C.dual N).subtype

/-- An element of the integral dual belongs to the embedded submodule exactly when
its ambient vector belongs to the original submodule. -/
theorem mem_insideDual_iff (C : IntegralLatticePair V) (N : Submodule ℤ V)
    (x : C.dual N) :
    x ∈ C.insideDual N ↔ (x : V) ∈ N := sorry

/-- The quotient of the integral dual by the embedded original submodule. -/
abbrev discriminantGroup (C : IntegralLatticePair V) (N : Submodule ℤ V) : Type u :=
  C.dual N ⧸ C.insideDual N

/-- The sum of the distinguished sublattice and its orthogonal lattice, as a
submodule of the ambient lattice. -/
def sumInsideLattice (C : IntegralLatticePair V) : Submodule ℤ C.lattice :=
  (C.sublattice ⊔ C.orthogonal).comap C.lattice.subtype

/-- An ambient lattice element belongs to the embedded sum exactly when its
ambient vector belongs to the sum of the sublattice and the orthogonal lattice. -/
theorem mem_sumInsideLattice_iff (C : IntegralLatticePair V) (x : C.lattice) :
    x ∈ C.sumInsideLattice ↔ (x : V) ∈ C.sublattice ⊔ C.orthogonal := sorry

/-- The sublattice projection sends the sum of the sublattice and the orthogonal
lattice into the sublattice embedded in its dual. -/
theorem sumInsideLattice_le_leftLift_comap (C : IntegralLatticePair V) :
    C.sumInsideLattice ≤ (C.insideDual C.sublattice).comap C.leftLift := sorry

/-- The orthogonal projection sends the sum of the sublattice and the orthogonal
lattice into the orthogonal lattice embedded in its dual. -/
theorem sumInsideLattice_le_rightLift_comap (C : IntegralLatticePair V) :
    C.sumInsideLattice ≤ (C.insideDual C.orthogonal).comap C.rightLift := sorry

/-- The map from the ambient lattice modulo the orthogonal sum to the sublattice
discriminant group induced by projection. -/
noncomputable def leftMap (C : IntegralLatticePair V) :
    (C.lattice ⧸ C.sumInsideLattice) →ₗ[ℤ] C.discriminantGroup C.sublattice :=
  C.sumInsideLattice.mapQ (C.insideDual C.sublattice) C.leftLift
    C.sumInsideLattice_le_leftLift_comap

/-- On quotient representatives, the map to the sublattice discriminant group is
given by the lift of rational sublattice projection. -/
theorem leftMap_mk (C : IntegralLatticePair V) (x : C.lattice) :
    C.leftMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (C.leftLift x) := sorry

/-- The map from the ambient lattice modulo the orthogonal sum to the orthogonal
lattice discriminant group induced by projection. -/
noncomputable def rightMap (C : IntegralLatticePair V) :
    (C.lattice ⧸ C.sumInsideLattice) →ₗ[ℤ] C.discriminantGroup C.orthogonal :=
  C.sumInsideLattice.mapQ (C.insideDual C.orthogonal) C.rightLift
    C.sumInsideLattice_le_rightLift_comap

/-- On quotient representatives, the map to the orthogonal lattice discriminant
group is given by the lift of rational orthogonal projection. -/
theorem rightMap_mk (C : IntegralLatticePair V) (x : C.lattice) :
    C.rightMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (C.rightLift x) := sorry

/-- The sublattice projection carries the ambient lattice dual into the sublattice dual. -/
theorem toSublatticeSpan_mem_dual_of_mem_dual (C : IntegralLatticePair V)
    (x : C.dual C.lattice) :
    C.toSublatticeSpan x ∈ C.dual C.sublattice := sorry

/-- The orthogonal projection carries the ambient lattice dual into the orthogonal lattice dual. -/
theorem toOrthogonalSpan_mem_dual_of_mem_dual (C : IntegralLatticePair V)
    (x : C.dual C.lattice) :
    C.toOrthogonalSpan x ∈ C.dual C.orthogonal := sorry

/-- The integral linear map from the ambient lattice dual to the sublattice dual
induced by rational projection. -/
noncomputable def leftDualMap (C : IntegralLatticePair V) :
    C.dual C.lattice →ₗ[ℤ] C.dual C.sublattice :=
  (((C.toSublatticeSpan.restrictScalars ℤ).domRestrict (C.dual C.lattice)).codRestrict
    (C.dual C.sublattice) C.toSublatticeSpan_mem_dual_of_mem_dual)

/-- The map between the ambient and sublattice duals agrees with rational
sublattice projection. -/
theorem leftDualMap_apply (C : IntegralLatticePair V) (x : C.dual C.lattice) :
    C.leftDualMap x = C.toSublatticeSpan x := sorry

/-- The integral linear map from the ambient lattice dual to the orthogonal lattice
dual induced by rational projection. -/
noncomputable def rightDualMap (C : IntegralLatticePair V) :
    C.dual C.lattice →ₗ[ℤ] C.dual C.orthogonal :=
  (((C.toOrthogonalSpan.restrictScalars ℤ).domRestrict (C.dual C.lattice)).codRestrict
    (C.dual C.orthogonal) C.toOrthogonalSpan_mem_dual_of_mem_dual)

/-- The map between the ambient and orthogonal lattice duals agrees with rational
orthogonal projection. -/
theorem rightDualMap_apply (C : IntegralLatticePair V) (x : C.dual C.lattice) :
    C.rightDualMap x = C.toOrthogonalSpan x := sorry

/-- The ambient lattice embedded in its dual maps into the range of the map to
the sublattice discriminant group. -/
theorem insideDual_le_leftCokernel_comap (C : IntegralLatticePair V) :
    C.insideDual C.lattice ≤ (LinearMap.range C.leftMap).comap
      ((C.insideDual C.sublattice).mkQ.comp C.leftDualMap) := sorry

/-- The ambient lattice embedded in its dual maps into the range of the map to
the orthogonal lattice discriminant group. -/
theorem insideDual_le_rightCokernel_comap (C : IntegralLatticePair V) :
    C.insideDual C.lattice ≤ (LinearMap.range C.rightMap).comap
      ((C.insideDual C.orthogonal).mkQ.comp C.rightDualMap) := sorry

/-- The induced map from the ambient discriminant group to the cokernel of the
map into the sublattice discriminant group. -/
noncomputable def leftCokernelMap (C : IntegralLatticePair V) :
    C.discriminantGroup C.lattice →ₗ[ℤ]
      C.discriminantGroup C.sublattice ⧸ LinearMap.range C.leftMap :=
  (C.insideDual C.lattice).mapQ (LinearMap.range C.leftMap)
    ((C.insideDual C.sublattice).mkQ.comp C.leftDualMap)
    C.insideDual_le_leftCokernel_comap

/-- On dual-lattice representatives, the left cokernel map is given by projection
to the sublattice dual followed by the two quotient maps. -/
theorem leftCokernelMap_mk (C : IntegralLatticePair V) (x : C.dual C.lattice) :
    C.leftCokernelMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((C.insideDual C.sublattice).mkQ (C.leftDualMap x)) := sorry

/-- The induced map from the ambient discriminant group to the cokernel of the
map into the orthogonal lattice discriminant group. -/
noncomputable def rightCokernelMap (C : IntegralLatticePair V) :
    C.discriminantGroup C.lattice →ₗ[ℤ]
      C.discriminantGroup C.orthogonal ⧸ LinearMap.range C.rightMap :=
  (C.insideDual C.lattice).mapQ (LinearMap.range C.rightMap)
    ((C.insideDual C.orthogonal).mkQ.comp C.rightDualMap)
    C.insideDual_le_rightCokernel_comap

/-- On dual-lattice representatives, the right cokernel map is given by projection
to the orthogonal lattice dual followed by the two quotient maps. -/
theorem rightCokernelMap_mk (C : IntegralLatticePair V) (x : C.dual C.lattice) :
    C.rightCokernelMap (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((C.insideDual C.orthogonal).mkQ (C.rightDualMap x)) := sorry

/-- The map from the ambient lattice modulo the orthogonal sum to the sublattice
discriminant group is injective. -/
theorem leftMap_injective (C : IntegralLatticePair V) :
    Function.Injective C.leftMap := sorry

/-- The map from the ambient lattice modulo the orthogonal sum to the orthogonal
lattice discriminant group is injective. -/
theorem rightMap_injective (C : IntegralLatticePair V) :
    Function.Injective C.rightMap := sorry

/-- The cokernel of the map to the sublattice discriminant group is a quotient
of the ambient discriminant group via the induced cokernel map. -/
theorem leftCokernelMap_surjective (C : IntegralLatticePair V) :
    Function.Surjective C.leftCokernelMap := sorry

/-- The cokernel of the map to the orthogonal lattice discriminant group is a
quotient of the ambient discriminant group via the induced cokernel map. -/
theorem rightCokernelMap_surjective (C : IntegralLatticePair V) :
    Function.Surjective C.rightCokernelMap := sorry

end IntegralLatticePair
