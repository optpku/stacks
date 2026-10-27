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
      (C.withSublattice N h_le h_torsionFree).sublattice = N := by
  exact ⟨rfl, rfl⟩

/-- The rational subspace spanned by an integral submodule. -/
def rationalSpan (N : Submodule ℤ V) : Submodule ℚ V :=
  Submodule.span ℚ (N : Set V)

private theorem exists_int_smul_mem_rationalSpan (N : Submodule ℤ V) {x : V}
    (hx : x ∈ rationalSpan N) : ∃ n : ℤ, n ≠ 0 ∧ n • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨m, hm, hmx⟩ := ihx
    obtain ⟨n, hn, hny⟩ := ihy
    refine ⟨m * n, mul_ne_zero hm hn, ?_⟩
    rw [smul_add]
    exact N.add_mem (by rw [mul_comm m n, mul_smul]; exact N.smul_mem n hmx)
      (by rw [mul_smul]; exact N.smul_mem m hny)
  | smul q x hx ih =>
    obtain ⟨n, hn, hnx⟩ := ih
    refine ⟨(q.den : ℤ) * n, mul_ne_zero (Int.natCast_ne_zero.mpr q.den_nz) hn, ?_⟩
    have hden : (q.den : ℚ) * q = (q.num : ℚ) := by
      simpa only [mul_comm] using
        (eq_div_iff (Nat.cast_ne_zero.mpr q.den_nz)).mp q.num_div_den.symm
    have heq : ((q.den : ℤ) * n) • (q • x) = q.num • (n • x) := by
      rw [mul_smul, smul_comm n q x, ← smul_assoc, zsmul_eq_mul, Int.cast_natCast, hden]
      exact Int.cast_smul_eq_zsmul ℚ _ _
    rw [heq]
    exact N.smul_mem q.num hnx

private theorem rationalSpan_lattice_inf (C : IntegralLatticePair V) (W : Submodule ℚ V) :
    rationalSpan (C.lattice ⊓ W.restrictScalars ℤ) = W := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (fun x hx ↦ hx.2)
  · intro x hx
    have hxspan : x ∈ rationalSpan C.lattice := by
      change x ∈ Submodule.span ℚ (C.lattice : Set V)
      rw [C.spans]
      trivial
    obtain ⟨n, hn, hnx⟩ := exists_int_smul_mem_rationalSpan C.lattice hxspan
    have hmem : n • x ∈ C.lattice ⊓ W.restrictScalars ℤ :=
      ⟨hnx, (W.restrictScalars ℤ).smul_mem n hx⟩
    have hnq : (n : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hn
    apply (Submodule.smul_mem_iff _ hnq).mp
    change (n : ℚ) • x ∈ Submodule.span ℚ
      ((C.lattice ⊓ W.restrictScalars ℤ) : Set V)
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.subset_span hmem

private theorem mem_sublattice_of_mem_rationalSpan (C : IntegralLatticePair V) {x : V}
    (hx : x ∈ C.lattice) (hxspan : x ∈ rationalSpan C.sublattice) : x ∈ C.sublattice := by
  letI := C.quotientTorsionFree
  obtain ⟨n, hn, hnx⟩ := exists_int_smul_mem_rationalSpan C.sublattice hxspan
  let A := C.sublattice.comap C.lattice.subtype
  let y : C.lattice := ⟨x, hx⟩
  have hzero : n • A.mkQ y = 0 :=
    (map_smul A.mkQ n y).symm.trans ((Submodule.Quotient.mk_eq_zero A).mpr hnx)
  have hq : A.mkQ y = 0 := (smul_eq_zero_iff_right hn).mp hzero
  exact (Submodule.Quotient.mk_eq_zero A).mp hq

/-- The integral dual of a submodule within its rational span, with respect to the pairing. -/
def dual (C : IntegralLatticePair V) (N : Submodule ℤ V) : Submodule ℤ V :=
  (rationalSpan N).restrictScalars ℤ ⊓ dualSubmodule C.form.flip N

/-- An element belongs to the integral dual exactly when it lies in the rational span
and pairs integrally with every element of the submodule. -/
theorem mem_dual_iff (C : IntegralLatticePair V) (N : Submodule ℤ V) (x : V) :
    x ∈ C.dual N ↔ x ∈ rationalSpan N ∧
      ∀ y ∈ N, C.form y x ∈ (1 : Submodule ℤ ℚ) := by
  rfl

/-- The integral lattice orthogonal to the distinguished sublattice. -/
def orthogonal (C : IntegralLatticePair V) : Submodule ℤ V :=
  C.lattice ⊓
    (C.form.orthogonal (rationalSpan C.sublattice)).restrictScalars ℤ

/-- An element belongs to the orthogonal lattice exactly when it belongs to the
ambient lattice and pairs to zero with every element of the distinguished sublattice. -/
theorem mem_orthogonal_iff (C : IntegralLatticePair V) (x : V) :
    x ∈ C.orthogonal ↔ x ∈ C.lattice ∧
      ∀ a ∈ C.sublattice, C.form a x = 0 := by
  change (x ∈ C.lattice ∧ ∀ a ∈ rationalSpan C.sublattice, C.form a x = 0) ↔ _
  constructor
  · intro h
    exact ⟨h.1, fun a ha ↦ h.2 a (Submodule.subset_span ha)⟩
  · intro h
    have hspan : rationalSpan C.sublattice ≤ LinearMap.ker (C.form.flip x) :=
      Submodule.span_le.mpr (fun a ha ↦ h.2 a ha)
    exact ⟨h.1, fun a ha ↦ hspan ha⟩

/-- The rational span of the distinguished sublattice and its orthogonal subspace
are complementary. -/
theorem isCompl_rationalSpan_orthogonal (C : IntegralLatticePair V) :
    IsCompl (rationalSpan C.sublattice)
      (C.form.orthogonal (rationalSpan C.sublattice)) := by
  letI := C.latticeFinite
  have hfg : (Submodule.span ℚ (C.lattice : Set V)).FG :=
    (Submodule.FG.of_finite (N := C.lattice)).span
  haveI : FiniteDimensional ℚ V := ⟨C.spans ▸ hfg⟩
  apply (LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint C.symmetric.isRefl).mpr
  apply Submodule.disjoint_def.mpr
  intro x hx ho
  by_contra hne
  exact (ne_of_gt (C.positiveDefinite x hne)) (ho x hx)

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
    C.toSublatticeSpan x ∈ rationalSpan C.sublattice := by
  classical
  simp only [toSublatticeSpan, dif_pos C.isCompl_rationalSpan_orthogonal,
    LinearMap.comp_apply, Submodule.coe_subtype]
  exact Subtype.property _

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

private theorem toSublatticeSpan_eq_projection (C : IntegralLatticePair V) :
    C.toSublatticeSpan = (rationalSpan C.sublattice).projection
      (C.form.orthogonal (rationalSpan C.sublattice)) C.isCompl_rationalSpan_orthogonal := by
  classical
  simp only [toSublatticeSpan, dif_pos C.isCompl_rationalSpan_orthogonal,
    Submodule.projection]

private theorem toOrthogonalSpan_eq_projection (C : IntegralLatticePair V) :
    C.toOrthogonalSpan = (C.form.orthogonal (rationalSpan C.sublattice)).projection
      (rationalSpan C.sublattice) C.isCompl_rationalSpan_orthogonal.symm := by
  classical
  simp only [toOrthogonalSpan, dif_pos C.isCompl_rationalSpan_orthogonal,
    Submodule.projection]

private theorem projection_add_projection (C : IntegralLatticePair V) (x : V) :
    C.toSublatticeSpan x + C.toOrthogonalSpan x = x := by
  rw [toSublatticeSpan_eq_projection, toOrthogonalSpan_eq_projection]
  exact Submodule.projection_add_projection_eq_self C.isCompl_rationalSpan_orthogonal x

private theorem form_toSublatticeSpan_right (C : IntegralLatticePair V) (a x : V)
    (ha : a ∈ rationalSpan C.sublattice) :
    C.form a (C.toSublatticeSpan x) = C.form a x := by
  have ho : C.form a (C.toOrthogonalSpan x) = 0 := by
    have hm : C.toOrthogonalSpan x ∈ C.form.orthogonal (rationalSpan C.sublattice) := by
      rw [toOrthogonalSpan_eq_projection]
      exact Submodule.projection_apply_mem _ x
    exact hm a ha
  have h := congrArg (C.form a) (projection_add_projection C x)
  simpa only [map_add, ho, add_zero] using h

private theorem form_toOrthogonalSpan_right (C : IntegralLatticePair V) (b x : V)
    (hb : b ∈ C.orthogonal) : C.form b (C.toOrthogonalSpan x) = C.form b x := by
  have ho : C.form b (C.toSublatticeSpan x) = 0 :=
    (C.symmetric.eq _ _).trans (hb.2 _ (C.toSublatticeSpan_mem x))
  have h := congrArg (C.form b) (projection_add_projection C x)
  simpa only [map_add, ho, zero_add] using h

/-- The orthogonal projection takes values in the rational span of the orthogonal lattice. -/
theorem toOrthogonalSpan_mem (C : IntegralLatticePair V) (x : V) :
    C.toOrthogonalSpan x ∈ rationalSpan C.orthogonal := by
  rw [orthogonal, rationalSpan_lattice_inf, toOrthogonalSpan_eq_projection]
  exact Submodule.projection_apply_mem _ x

/-- Projection of an ambient lattice element onto the sublattice span belongs to
the integral dual of the sublattice. -/
theorem toSublatticeSpan_mem_dual (C : IntegralLatticePair V) (x : C.lattice) :
    C.toSublatticeSpan x ∈ C.dual C.sublattice := by
  refine (C.mem_dual_iff _ _).mpr ⟨C.toSublatticeSpan_mem x, ?_⟩
  intro a ha
  rw [form_toSublatticeSpan_right C a x (Submodule.subset_span ha)]
  exact C.integral a (C.sublatticeLe ha) x x.property

/-- Projection of an ambient lattice element onto the orthogonal subspace belongs
to the integral dual of the orthogonal lattice. -/
theorem toOrthogonalSpan_mem_dual (C : IntegralLatticePair V) (x : C.lattice) :
    C.toOrthogonalSpan x ∈ C.dual C.orthogonal := by
  refine (C.mem_dual_iff _ _).mpr ⟨C.toOrthogonalSpan_mem x, ?_⟩
  intro b hb
  rw [form_toOrthogonalSpan_right C b x hb]
  exact C.integral b hb.1 x x.property

/-- The integral linear map from the ambient lattice into the sublattice dual
induced by rational orthogonal projection. -/
noncomputable def leftLift (C : IntegralLatticePair V) :
    C.lattice →ₗ[ℤ] C.dual C.sublattice :=
  (((C.toSublatticeSpan.restrictScalars ℤ).domRestrict C.lattice).codRestrict
    (C.dual C.sublattice) C.toSublatticeSpan_mem_dual)

/-- The lift into the sublattice dual agrees with the rational sublattice projection. -/
theorem leftLift_apply (C : IntegralLatticePair V) (x : C.lattice) :
    C.leftLift x = C.toSublatticeSpan x := by
  rfl

/-- The integral linear map from the ambient lattice into the orthogonal lattice dual
induced by rational orthogonal projection. -/
noncomputable def rightLift (C : IntegralLatticePair V) :
    C.lattice →ₗ[ℤ] C.dual C.orthogonal :=
  (((C.toOrthogonalSpan.restrictScalars ℤ).domRestrict C.lattice).codRestrict
    (C.dual C.orthogonal) C.toOrthogonalSpan_mem_dual)

/-- The lift into the orthogonal lattice dual agrees with the rational orthogonal projection. -/
theorem rightLift_apply (C : IntegralLatticePair V) (x : C.lattice) :
    C.rightLift x = C.toOrthogonalSpan x := by
  rfl

/-- The submodule of an integral dual consisting of elements of the original submodule. -/
def insideDual (C : IntegralLatticePair V) (N : Submodule ℤ V) :
    Submodule ℤ (C.dual N) :=
  N.comap (C.dual N).subtype

/-- An element of the integral dual belongs to the embedded submodule exactly when
its ambient vector belongs to the original submodule. -/
theorem mem_insideDual_iff (C : IntegralLatticePair V) (N : Submodule ℤ V)
    (x : C.dual N) :
    x ∈ C.insideDual N ↔ (x : V) ∈ N := by
  rfl

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
    x ∈ C.sumInsideLattice ↔ (x : V) ∈ C.sublattice ⊔ C.orthogonal := by
  rfl

/-- The sublattice projection sends the sum of the sublattice and the orthogonal
lattice into the sublattice embedded in its dual. -/
theorem sumInsideLattice_le_leftLift_comap (C : IntegralLatticePair V) :
    C.sumInsideLattice ≤ (C.insideDual C.sublattice).comap C.leftLift := by
  intro x hx
  change (C.leftLift x : V) ∈ C.sublattice
  rw [C.leftLift_apply]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((C.mem_sumInsideLattice_iff x).mp hx)
  have hA : C.toSublatticeSpan a = a := by
    rw [toSublatticeSpan_eq_projection]
    exact Submodule.projection_apply_of_mem_left _ (Submodule.subset_span ha)
  have hB : C.toSublatticeSpan b = 0 := by
    rw [toSublatticeSpan_eq_projection]
    exact Submodule.projection_apply_of_mem_right _ hb.2
  rw [← hab, map_add, hA, hB, add_zero]
  exact ha

/-- The orthogonal projection sends the sum of the sublattice and the orthogonal
lattice into the orthogonal lattice embedded in its dual. -/
theorem sumInsideLattice_le_rightLift_comap (C : IntegralLatticePair V) :
    C.sumInsideLattice ≤ (C.insideDual C.orthogonal).comap C.rightLift := by
  intro x hx
  change (C.rightLift x : V) ∈ C.orthogonal
  rw [C.rightLift_apply]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp ((C.mem_sumInsideLattice_iff x).mp hx)
  have hA : C.toOrthogonalSpan a = 0 := by
    rw [toOrthogonalSpan_eq_projection]
    exact Submodule.projection_apply_of_mem_right _ (Submodule.subset_span ha)
  have hB : C.toOrthogonalSpan b = b := by
    rw [toOrthogonalSpan_eq_projection]
    exact Submodule.projection_apply_of_mem_left _ hb.2
  rw [← hab, map_add, hA, hB, zero_add]
  exact hb

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
      Submodule.Quotient.mk (C.leftLift x) := by
  rfl

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
      Submodule.Quotient.mk (C.rightLift x) := by
  rfl

/-- The sublattice projection carries the ambient lattice dual into the sublattice dual. -/
theorem toSublatticeSpan_mem_dual_of_mem_dual (C : IntegralLatticePair V)
    (x : C.dual C.lattice) :
    C.toSublatticeSpan x ∈ C.dual C.sublattice := by
  refine (C.mem_dual_iff _ _).mpr ⟨C.toSublatticeSpan_mem x, ?_⟩
  intro a ha
  rw [form_toSublatticeSpan_right C a x (Submodule.subset_span ha)]
  exact ((C.mem_dual_iff _ _).mp x.property).2 a (C.sublatticeLe ha)

/-- The orthogonal projection carries the ambient lattice dual into the orthogonal lattice dual. -/
theorem toOrthogonalSpan_mem_dual_of_mem_dual (C : IntegralLatticePair V)
    (x : C.dual C.lattice) :
    C.toOrthogonalSpan x ∈ C.dual C.orthogonal := by
  refine (C.mem_dual_iff _ _).mpr ⟨C.toOrthogonalSpan_mem x, ?_⟩
  intro b hb
  rw [form_toOrthogonalSpan_right C b x hb]
  exact ((C.mem_dual_iff _ _).mp x.property).2 b hb.1

/-- The integral linear map from the ambient lattice dual to the sublattice dual
induced by rational projection. -/
noncomputable def leftDualMap (C : IntegralLatticePair V) :
    C.dual C.lattice →ₗ[ℤ] C.dual C.sublattice :=
  (((C.toSublatticeSpan.restrictScalars ℤ).domRestrict (C.dual C.lattice)).codRestrict
    (C.dual C.sublattice) C.toSublatticeSpan_mem_dual_of_mem_dual)

/-- The map between the ambient and sublattice duals agrees with rational
sublattice projection. -/
theorem leftDualMap_apply (C : IntegralLatticePair V) (x : C.dual C.lattice) :
    C.leftDualMap x = C.toSublatticeSpan x := by
  rfl

/-- The integral linear map from the ambient lattice dual to the orthogonal lattice
dual induced by rational projection. -/
noncomputable def rightDualMap (C : IntegralLatticePair V) :
    C.dual C.lattice →ₗ[ℤ] C.dual C.orthogonal :=
  (((C.toOrthogonalSpan.restrictScalars ℤ).domRestrict (C.dual C.lattice)).codRestrict
    (C.dual C.orthogonal) C.toOrthogonalSpan_mem_dual_of_mem_dual)

/-- The map between the ambient and orthogonal lattice duals agrees with rational
orthogonal projection. -/
theorem rightDualMap_apply (C : IntegralLatticePair V) (x : C.dual C.lattice) :
    C.rightDualMap x = C.toOrthogonalSpan x := by
  rfl

/-- The ambient lattice embedded in its dual maps into the range of the map to
the sublattice discriminant group. -/
theorem insideDual_le_leftCokernel_comap (C : IntegralLatticePair V) :
    C.insideDual C.lattice ≤ (LinearMap.range C.leftMap).comap
      ((C.insideDual C.sublattice).mkQ.comp C.leftDualMap) := by
  intro x hx
  change (C.insideDual C.sublattice).mkQ (C.leftDualMap x) ∈ LinearMap.range C.leftMap
  refine ⟨Submodule.Quotient.mk (⟨x, hx⟩ : C.lattice), ?_⟩
  rw [C.leftMap_mk]
  congr 1

/-- The ambient lattice embedded in its dual maps into the range of the map to
the orthogonal lattice discriminant group. -/
theorem insideDual_le_rightCokernel_comap (C : IntegralLatticePair V) :
    C.insideDual C.lattice ≤ (LinearMap.range C.rightMap).comap
      ((C.insideDual C.orthogonal).mkQ.comp C.rightDualMap) := by
  intro x hx
  change (C.insideDual C.orthogonal).mkQ (C.rightDualMap x) ∈ LinearMap.range C.rightMap
  refine ⟨Submodule.Quotient.mk (⟨x, hx⟩ : C.lattice), ?_⟩
  rw [C.rightMap_mk]
  congr 1

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
      Submodule.Quotient.mk ((C.insideDual C.sublattice).mkQ (C.leftDualMap x)) := by
  rfl

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
      Submodule.Quotient.mk ((C.insideDual C.orthogonal).mkQ (C.rightDualMap x)) := by
  rfl

/-- The map from the ambient lattice modulo the orthogonal sum to the sublattice
discriminant group is injective. -/
theorem leftMap_injective (C : IntegralLatticePair V) :
    Function.Injective C.leftMap := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  revert hz
  refine Submodule.Quotient.induction_on _ z ?_
  intro x hx
  change (Submodule.Quotient.mk x : C.lattice ⧸ C.sumInsideLattice) = 0
  have hA : C.toSublatticeSpan x ∈ C.sublattice := by
    rw [LinearMap.mem_ker, C.leftMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    exact hx
  have hB : C.toOrthogonalSpan x ∈ C.orthogonal := by
    refine ⟨?_, ?_⟩
    · have heq : C.toOrthogonalSpan x = x - C.toSublatticeSpan x := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact projection_add_projection C x
      rw [heq]
      exact C.lattice.sub_mem x.property (C.sublatticeLe hA)
    · have hm := C.toOrthogonalSpan_mem x
      rwa [orthogonal, rationalSpan_lattice_inf] at hm
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (C.mem_sumInsideLattice_iff x).mpr
  rw [← projection_add_projection C x]
  exact Submodule.add_mem_sup hA hB

/-- The map from the ambient lattice modulo the orthogonal sum to the orthogonal
lattice discriminant group is injective. -/
theorem rightMap_injective (C : IntegralLatticePair V) :
    Function.Injective C.rightMap := by
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  revert hz
  refine Submodule.Quotient.induction_on _ z ?_
  intro x hx
  change (Submodule.Quotient.mk x : C.lattice ⧸ C.sumInsideLattice) = 0
  have hB : C.toOrthogonalSpan x ∈ C.orthogonal := by
    rw [LinearMap.mem_ker, C.rightMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    exact hx
  have hA : C.toSublatticeSpan x ∈ C.sublattice := by
    apply mem_sublattice_of_mem_rationalSpan C
    · have heq : C.toSublatticeSpan x = x - C.toOrthogonalSpan x := by
        rw [eq_sub_iff_add_eq]
        exact projection_add_projection C x
      rw [heq]
      exact C.lattice.sub_mem x.property hB.1
    · exact C.toSublatticeSpan_mem x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (C.mem_sumInsideLattice_iff x).mpr
  rw [← projection_add_projection C x]
  exact Submodule.add_mem_sup hA hB

/-- The cokernel of the map to the sublattice discriminant group is a quotient
of the ambient discriminant group via the induced cokernel map. -/
theorem leftCokernelMap_surjective (C : IntegralLatticePair V) :
    Function.Surjective C.leftCokernelMap := sorry

/-- The cokernel of the map to the orthogonal lattice discriminant group is a
quotient of the ambient discriminant group via the induced cokernel map. -/
theorem rightCokernelMap_surjective (C : IntegralLatticePair V) :
    Function.Surjective C.rightCokernelMap := sorry

end IntegralLatticePair
