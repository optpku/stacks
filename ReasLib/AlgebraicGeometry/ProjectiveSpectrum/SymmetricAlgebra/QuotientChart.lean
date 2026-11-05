/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.SymmetricAlgebra.Augmentation
public import ReasLib.RingTheory.GradedAlgebra.HomogeneousLocalization.Algebra
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Affine
public import Mathlib.LinearAlgebra.TensorAlgebra.Grading

/-!
# Quotient charts for symmetric projective spectra

A split quotient of a module by the base ring determines its symmetric-algebra
standard open.  The chart stores only the quotient and a lift of `1`; all
graded coordinates and fraction maps are derived from those data.
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry.Proj

/-- A split quotient of a module onto the base ring. -/
structure SymmetricQuotientChart
    (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] where
  /-- The linear quotient defining the chart. -/
  quotient : M →ₗ[R] R
  /-- A chosen lift of the unit in the quotient. -/
  generatorLift : M
  /-- The chosen lift maps to the unit. -/
  generatorLift_spec : quotient generatorLift = 1

namespace SymmetricQuotientChart

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- Construct a symmetric quotient chart from a quotient and a lift of its unit. -/
def ofQuotient (quotient : M →ₗ[R] R) (generatorLift : M)
    (generatorLift_spec : quotient generatorLift = 1) :
    SymmetricQuotientChart R M :=
  ⟨quotient, generatorLift, generatorLift_spec⟩

/-- The canonical grading of the symmetric algebra by powers of its degree-one image. -/
abbrev grading (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M] :
    ℕ → Submodule R (SymmetricAlgebra R M) :=
  (LinearMap.range (SymmetricAlgebra.ι R M : M →ₗ[R] SymmetricAlgebra R M) ^ ·)

/-- The degree-one generator map into the direct sum of the canonical graded pieces. -/
noncomputable def gradedAlgebraGenerator :
    M →ₗ[R] DirectSum ℕ (fun n ↦ ↥(grading R M n)) :=
  DirectSum.lof R ℕ (fun n ↦ ↥(grading R M n)) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ fun x ↦ by
      simp [grading]

/-- The homogeneous decomposition map of the symmetric algebra. -/
noncomputable def gradedAlgebraDecompose :
    SymmetricAlgebra R M →ₐ[R] DirectSum ℕ (fun n ↦ ↥(grading R M n)) :=
  SymmetricAlgebra.lift gradedAlgebraGenerator

/-- Recombining the homogeneous decomposition is the identity. -/
theorem gradedAlgebraDecompose_rightInv :
    (DirectSum.coeAlgHom (grading R M)).comp gradedAlgebraDecompose =
      AlgHom.id R (SymmetricAlgebra R M) := by
  ext m
  simp [gradedAlgebraDecompose, gradedAlgebraGenerator, DirectSum.lof_eq_of]

/-- A homogeneous element decomposes into its given direct-sum component. -/
theorem gradedAlgebraDecompose_leftInv (n : ℕ) (x : grading R M n) :
    gradedAlgebraDecompose x = DirectSum.of (fun d ↦ ↥(grading R M d)) n x := by
  obtain ⟨x, hx⟩ := x
  change SymmetricAlgebra.lift gradedAlgebraGenerator x = _
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, DirectSum.algebraMap_apply]
    rfl
  | add x y i hx hy ihx ihy =>
    rw [map_add, ihx, ihy, ← map_add]
    rfl
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, ih, SymmetricAlgebra.lift_ι_apply]
    change DirectSum.of _ 1 _ * DirectSum.of _ i _ = _
    rw [DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/-- The powers-of-degree-one decomposition gives the canonical grading on a symmetric algebra. -/
noncomputable instance gradingGradedAlgebra : GradedAlgebra (grading R M) :=
  GradedAlgebra.ofAlgHom (grading R M) gradedAlgebraDecompose
    gradedAlgebraDecompose_rightInv gradedAlgebraDecompose_leftInv

/-- Symmetric-algebra generators are homogeneous of degree one. -/
theorem generator_mem_degreeOne (x : M) :
    SymmetricAlgebra.ι R M x ∈ grading R M 1 := by
  simpa only [grading, pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) x

/-- Projection onto the kernel determined by the chosen splitting of the quotient. -/
def kernelProjection (C : SymmetricQuotientChart R M) :
    M →ₗ[R] LinearMap.ker C.quotient where
  toFun x := ⟨x - C.quotient x • C.generatorLift, by
    simp [C.generatorLift_spec]⟩
  map_add' x y := by
    apply Subtype.ext
    change x + y - C.quotient (x + y) • C.generatorLift = _
    simp [map_add, add_smul, sub_add_sub_comm]
  map_smul' r x := by
    apply Subtype.ext
    change r • x - C.quotient (r • x) • C.generatorLift = _
    simp [map_smul, smul_sub, smul_smul]

/-- The split coordinates recover a vector from its kernel and quotient components. -/
theorem kernelProjection_add_quotient_smul (C : SymmetricQuotientChart R M) (x : M) :
    (C.kernelProjection x : M) + C.quotient x • C.generatorLift = x := by
  exact sub_add_cancel x (C.quotient x • C.generatorLift)

/-- Evaluating the quotient coordinate at `1` and retaining the kernel coordinates. -/
def evaluation (C : SymmetricQuotientChart R M) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (LinearMap.ker C.quotient) :=
  SymmetricAlgebra.lift
    { toFun := fun x ↦
        SymmetricAlgebra.ι R (LinearMap.ker C.quotient) (C.kernelProjection x) +
          algebraMap R (SymmetricAlgebra R (LinearMap.ker C.quotient)) (C.quotient x)
      map_add' := by
        intro x y
        simp [map_add, add_add_add_comm]
      map_smul' := by
        intro r x
        simp [map_smul, Algebra.smul_def, mul_add] }

/-- The fixed evaluation uses the kernel projection for the chart's chosen lift. -/
theorem evaluation_ι (C : SymmetricQuotientChart R M) (x : M) :
    C.evaluation (SymmetricAlgebra.ι R M x) =
      SymmetricAlgebra.ι R (LinearMap.ker C.quotient)
          ⟨x - C.quotient x • C.generatorLift, by simp [C.generatorLift_spec]⟩ +
        algebraMap R (SymmetricAlgebra R (LinearMap.ker C.quotient)) (C.quotient x) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Evaluate using the splitting determined by the specified lift of the quotient unit. -/
def evaluationAt (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (LinearMap.ker C.quotient) :=
  let p : M →ₗ[R] LinearMap.ker C.quotient :=
    ({ C with generatorLift := s, generatorLift_spec := hs } :
      SymmetricQuotientChart R M).kernelProjection
  SymmetricAlgebra.lift
    ((SymmetricAlgebra.ι R (LinearMap.ker C.quotient)).comp p +
      (Algebra.linearMap R (SymmetricAlgebra R (LinearMap.ker C.quotient))).comp C.quotient)

/-- Specifying a lift agrees with updating the chart's chosen lift before evaluation. -/
theorem evaluationAt_eq_evaluation_update (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) :
    C.evaluationAt s hs =
      ({ C with generatorLift := s, generatorLift_spec := hs } :
        SymmetricQuotientChart R M).evaluation := by
  ext x
  rfl

/-- Evaluation at the originally chosen lift recovers the fixed evaluation. -/
theorem evaluationAt_generatorLift (C : SymmetricQuotientChart R M) :
    C.evaluationAt C.generatorLift C.generatorLift_spec = C.evaluation := by
  ext x
  rfl

/-- The coordinate formula for evaluation with respect to a specified splitting. -/
theorem evaluationAt_ι (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) (x : M) :
    C.evaluationAt s hs (SymmetricAlgebra.ι R M x) =
      SymmetricAlgebra.ι R (LinearMap.ker C.quotient)
          ⟨x - C.quotient x • s, by simp [hs]⟩ +
        algebraMap R (SymmetricAlgebra R (LinearMap.ker C.quotient)) (C.quotient x) :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Evaluation retains every kernel coordinate. -/
theorem evaluationAt_ι_kernel (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) (k : LinearMap.ker C.quotient) :
    C.evaluationAt s hs (SymmetricAlgebra.ι R M k.1) =
      SymmetricAlgebra.ι R (LinearMap.ker C.quotient) k := by
  rw [evaluationAt_ι]
  simp [LinearMap.mem_ker.mp k.property]

/-- The homogeneous element inverted by the chart. -/
def denominatorAt (_ : SymmetricQuotientChart R M) (s : M) :
    SymmetricAlgebra R M :=
  SymmetricAlgebra.ι R M s

/-- A chart denominator is homogeneous of degree one. -/
theorem denominatorAt_mem_degreeOne (C : SymmetricQuotientChart R M) (s : M) :
    C.denominatorAt s ∈ grading R M 1 :=
  generator_mem_degreeOne s

/-- The homogeneous element inverted by the chosen quotient splitting. -/
def denominator (C : SymmetricQuotientChart R M) : SymmetricAlgebra R M :=
  C.denominatorAt C.generatorLift

/-- The degree-zero homogeneous localization for a specified lift of the quotient unit. -/
abbrev awayAt (C : SymmetricQuotientChart R M) (s : M) :=
  HomogeneousLocalization.Away (grading R M) (C.denominatorAt s)

/-- The degree-zero homogeneous localization for the chosen lift. -/
abbrev away (C : SymmetricQuotientChart R M) := C.awayAt C.generatorLift

/-- Evaluation with respect to the specified lift sends that denominator to `1`. -/
theorem evaluation_denominatorAt (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) :
    C.evaluationAt s hs (C.denominatorAt s) = 1 := by
  rw [denominatorAt, evaluationAt_ι]
  have hzero : (⟨s - C.quotient s • s, by simp [hs]⟩ : LinearMap.ker C.quotient) = 0 := by
    apply Subtype.ext
    simp [hs]
  rw [hzero, map_zero, hs, map_one, zero_add]

/-- The fixed evaluation sends its own chosen denominator to `1`. -/
theorem evaluation_denominator (C : SymmetricQuotientChart R M) :
    C.evaluation C.denominator = 1 := by
  rw [denominator, ← C.evaluationAt_generatorLift]
  exact C.evaluation_denominatorAt C.generatorLift C.generatorLift_spec

/-- The inclusion of a homogeneous localization into the ordinary localization. -/
def awayValRingHom (C : SymmetricQuotientChart R M) (s : M) :
    C.awayAt s →+* Localization.Away (C.denominatorAt s) where
  toFun := HomogeneousLocalization.val
  map_one' := HomogeneousLocalization.val_one
  map_mul' := HomogeneousLocalization.val_mul
  map_zero' := HomogeneousLocalization.val_zero
  map_add' := HomogeneousLocalization.val_add

/-- Evaluation on the ordinary localization obtained by sending the denominator to `1`. -/
noncomputable def awayEvaluation (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) :
    Localization.Away (C.denominatorAt s) →+*
      SymmetricAlgebra R (LinearMap.ker C.quotient) :=
  Localization.awayLift (C.evaluationAt s hs).toRingHom (C.denominatorAt s) (by
    change IsUnit (C.evaluationAt s hs (C.denominatorAt s))
    rw [C.evaluation_denominatorAt s hs]
    exact isUnit_one)

/-- Evaluation of an ordinary fraction uses the fact that its denominator evaluates to `1`. -/
theorem awayEvaluation_mk (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) (n : ℕ) (a : SymmetricAlgebra R M) :
    C.awayEvaluation s hs
        (Localization.mk a ⟨C.denominatorAt s ^ n, n, rfl⟩) =
      C.evaluationAt s hs a := by
  have hv : (C.evaluationAt s hs).toRingHom (C.denominatorAt s) * 1 = 1 := by
    change C.evaluationAt s hs (C.denominatorAt s) * 1 = 1
    rw [mul_one, C.evaluation_denominatorAt s hs]
  have h := Localization.awayLift_mk (C.evaluationAt s hs).toRingHom
    (C.denominatorAt s) a 1 hv n
  change C.awayEvaluation s hs
    (Localization.mk a ⟨C.denominatorAt s ^ n, n, rfl⟩) =
      C.evaluationAt s hs a * 1 ^ n at h
  simpa only [one_pow, mul_one] using h

/-- The forward coordinate map from the standard open to the symmetric algebra of the kernel. -/
noncomputable def standardOpenHom (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) :
    C.awayAt s →ₐ[R] SymmetricAlgebra R (LinearMap.ker C.quotient) where
  __ := (C.awayEvaluation s hs).comp (C.awayValRingHom s)
  commutes' r := by
    change C.awayEvaluation s hs
      (Localization.mk (algebraMap R (SymmetricAlgebra R M) r) 1) = _
    rw [Localization.mk_one_eq_algebraMap, awayEvaluation, Localization.awayLift,
      IsLocalization.Away.lift_eq]
    exact (C.evaluationAt s hs).commutes r

/-- The standard-open map evaluates a homogeneous numerator after setting the lift to `1`. -/
theorem standardOpenHom_mk (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) (n : ℕ) (a : SymmetricAlgebra R M)
    (ha : a ∈ grading R M n) :
    C.standardOpenHom s hs
        (HomogeneousLocalization.Away.mk (grading R M) (C.denominatorAt_mem_degreeOne s) n a
          (by simpa using ha)) =
      C.evaluationAt s hs a := by
  change C.awayEvaluation s hs
    (HomogeneousLocalization.Away.mk (grading R M) (C.denominatorAt_mem_degreeOne s) n a
      (by simpa using ha)).val = C.evaluationAt s hs a
  rw [HomogeneousLocalization.Away.val_mk]
  exact C.awayEvaluation_mk s hs n a

/-- The homogeneous fraction `k / s` associated to a kernel element. -/
def fractionLinear (C : SymmetricQuotientChart R M) (s : M) :
    LinearMap.ker C.quotient →ₗ[R] C.awayAt s where
  toFun k := HomogeneousLocalization.Away.mk (grading R M)
    (C.denominatorAt_mem_degreeOne s) 1 (SymmetricAlgebra.ι R M k.1)
      (generator_mem_degreeOne k.1)
  map_add' k l := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, map_add, Localization.add_mk_self]
  map_smul' r k := by
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, map_smul, Localization.smul_mk]

/-- A kernel fraction evaluates to its kernel generator. -/
theorem standardOpenHom_fractionLinear (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) (k : LinearMap.ker C.quotient) :
    C.standardOpenHom s hs (C.fractionLinear s k) =
      SymmetricAlgebra.ι R (LinearMap.ker C.quotient) k := by
  change C.standardOpenHom s hs
    (HomogeneousLocalization.Away.mk (grading R M) (C.denominatorAt_mem_degreeOne s) 1
      (SymmetricAlgebra.ι R M k.1) (generator_mem_degreeOne k.1)) = _
  rw [C.standardOpenHom_mk s hs 1 (SymmetricAlgebra.ι R M k.1) (generator_mem_degreeOne k.1)]
  exact C.evaluationAt_ι_kernel s hs k

/-- The inverse coordinate map, obtained from the universal property of the symmetric algebra. -/
def standardOpenInv (C : SymmetricQuotientChart R M) (s : M) :
    SymmetricAlgebra R (LinearMap.ker C.quotient) →ₐ[R] C.awayAt s :=
  SymmetricAlgebra.lift (C.fractionLinear s)

/-- The inverse coordinate map sends a kernel generator to the actual fraction `k / s`. -/
theorem standardOpenInv_ι (C : SymmetricQuotientChart R M) (s : M)
    (k : LinearMap.ker C.quotient) :
    C.standardOpenInv s (SymmetricAlgebra.ι R (LinearMap.ker C.quotient) k) =
      C.fractionLinear s k :=
  SymmetricAlgebra.lift_ι_apply _ _

/-- Re-homogenizing an evaluated generator gives its degree-one fraction. -/
theorem standardOpenInv_evaluationAt_ι (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) (x : M) :
    C.standardOpenInv s (C.evaluationAt s hs (SymmetricAlgebra.ι R M x)) =
      HomogeneousLocalization.Away.mk (grading R M) (C.denominatorAt_mem_degreeOne s) 1
        (SymmetricAlgebra.ι R M x) (generator_mem_degreeOne x) := by
  rw [evaluationAt_ι, map_add]
  simp only [standardOpenInv, SymmetricAlgebra.lift_ι_apply, AlgHom.commutes]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_add]
  change Localization.mk (S := Submonoid.powers (C.denominatorAt s))
      (SymmetricAlgebra.ι R M (x - C.quotient x • s))
      ⟨C.denominatorAt s ^ 1, 1, rfl⟩ +
      Localization.mk (S := Submonoid.powers (C.denominatorAt s))
        (algebraMap R (SymmetricAlgebra R M) (C.quotient x)) 1 =
    Localization.mk (S := Submonoid.powers (C.denominatorAt s))
      (SymmetricAlgebra.ι R M x) ⟨C.denominatorAt s ^ 1, 1, rfl⟩
  simp only [Localization.add_mk, Submonoid.coe_one, mul_one, one_mul]
  congr 1
  simp only [pow_one, denominatorAt, map_sub, map_smul, Algebra.smul_def]
  rw [mul_comm (SymmetricAlgebra.ι R M s)
    (algebraMap R (SymmetricAlgebra R M) (C.quotient x))]
  exact (add_comm _ _).trans (sub_add_cancel _ _)

/-- Re-homogenizing an evaluated homogeneous numerator gives its standard-open fraction. -/
theorem standardOpenInv_evaluationAt_homogeneous (C : SymmetricQuotientChart R M) (s : M)
    (hs : C.quotient s = 1) (n : ℕ) (a : grading R M n) :
    C.standardOpenInv s (C.evaluationAt s hs a.1) =
      HomogeneousLocalization.Away.mk (grading R M) (C.denominatorAt_mem_degreeOne s) n a.1
        (by simpa using a.property) := by
  obtain ⟨a, ha⟩ := a
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, AlgHom.commutes]
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk]
    change Localization.mk (S := Submonoid.powers (C.denominatorAt s))
        (algebraMap R (SymmetricAlgebra R M) r) 1 =
      Localization.mk (S := Submonoid.powers (C.denominatorAt s))
        (algebraMap R (SymmetricAlgebra R M) r) ⟨C.denominatorAt s ^ 0, 0, rfl⟩
    apply congrArg (Localization.mk (S := Submonoid.powers (C.denominatorAt s))
      (algebraMap R (SymmetricAlgebra R M) r))
    apply Subtype.ext
    simp only [Submonoid.coe_one, pow_zero]
  | add a b n ha hb iha ihb =>
    rw [map_add, map_add, iha, ihb]
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, Localization.add_mk_self]
  | mem_mul a ha n b hb ih =>
    obtain ⟨x, rfl⟩ := ha
    rw [map_mul, map_mul, standardOpenInv_evaluationAt_ι, ih]
    apply HomogeneousLocalization.val_injective
    simp [HomogeneousLocalization.Away.val_mk, Localization.mk_mul, pow_succ, mul_comm]

/-- The forward and inverse standard-open coordinate maps are inverse. -/
theorem standardOpenMaps_inverse (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) :
    Function.LeftInverse (C.standardOpenInv s) (C.standardOpenHom s hs) ∧
      Function.LeftInverse (C.standardOpenHom s hs) (C.standardOpenInv s) := by
  constructor
  · intro x
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (grading R M) (C.denominatorAt_mem_degreeOne s) x
    rw [C.standardOpenHom_mk s hs n a (by simpa using ha)]
    exact C.standardOpenInv_evaluationAt_homogeneous s hs n ⟨a, by simpa using ha⟩
  · have h : (C.standardOpenHom s hs).comp (C.standardOpenInv s) =
        AlgHom.id R (SymmetricAlgebra R (LinearMap.ker C.quotient)) := by
      ext k
      change C.standardOpenHom s hs
        (SymmetricAlgebra.lift (C.fractionLinear s) (SymmetricAlgebra.ι R _ k)) = _
      rw [SymmetricAlgebra.lift_ι_apply]
      exact C.standardOpenHom_fractionLinear s hs k
    intro a
    exact DFunLike.congr_fun h a

/-- A split quotient identifies its symmetric standard open with the symmetric algebra of its
kernel. -/
noncomputable def standardOpenEquiv (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) :
    C.awayAt s ≃ₐ[R] SymmetricAlgebra R (LinearMap.ker C.quotient) where
  toFun := C.standardOpenHom s hs
  invFun := C.standardOpenInv s
  left_inv := (C.standardOpenMaps_inverse s hs).1
  right_inv := (C.standardOpenMaps_inverse s hs).2
  map_mul' := map_mul (C.standardOpenHom s hs)
  map_add' := map_add (C.standardOpenHom s hs)
  commutes' := (C.standardOpenHom s hs).commutes

/-- The standard-open equivalence sends `k / s` to the corresponding kernel generator. -/
theorem standardOpenEquiv_fraction (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) (k : LinearMap.ker C.quotient) :
    C.standardOpenEquiv s hs (C.fractionLinear s k) =
      SymmetricAlgebra.ι R (LinearMap.ker C.quotient) k :=
  C.standardOpenHom_fractionLinear s hs k

/-- The homogeneous fraction `k / s` for a specified lift of the quotient unit. -/
def symmetricQuotientFractionAt (C : SymmetricQuotientChart R M)
    (s : M) (k : LinearMap.ker C.quotient) : C.awayAt s :=
  C.fractionLinear s k

/-- The homogeneous fraction `k / s` for the chosen lift of the quotient unit. -/
def symmetricQuotientFraction (C : SymmetricQuotientChart R M)
    (k : LinearMap.ker C.quotient) : C.away :=
  C.symmetricQuotientFractionAt C.generatorLift k

/-- The standard-open coordinate of `k / s` lies in the augmentation ideal. -/
theorem symmetricQuotientFraction_mem_conormalIdeal
    (C : SymmetricQuotientChart R M) (k : LinearMap.ker C.quotient) :
    C.standardOpenEquiv C.generatorLift C.generatorLift_spec
        (C.symmetricQuotientFraction k) ∈
      SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient) := by
  change C.standardOpenEquiv C.generatorLift C.generatorLift_spec
    (C.fractionLinear C.generatorLift k) ∈ _
  rw [C.standardOpenEquiv_fraction]
  exact SymmetricAlgebra.algebraMapInv_ι k

/-- The standard-open image of the homogeneous fraction `k / s`, regarded as an element of
the augmentation ideal. -/
def symmetricQuotientConormalNumerator (C : SymmetricQuotientChart R M)
    (k : LinearMap.ker C.quotient) :
    SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient) :=
  ⟨C.standardOpenEquiv C.generatorLift C.generatorLift_spec
      (C.symmetricQuotientFraction k),
    C.symmetricQuotientFraction_mem_conormalIdeal k⟩

/-- The conormal class represented by the homogeneous fraction `k / s`. -/
def symmetricQuotientFractionClass (C : SymmetricQuotientChart R M)
    (k : LinearMap.ker C.quotient) :
    (SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient)).Cotangent :=
  (SymmetricAlgebra.augmentationIdeal R
    (LinearMap.ker C.quotient)).toCotangent (C.symmetricQuotientConormalNumerator k)

/-- Replacing the lift gives the same class in the common augmentation cotangent module.
This compares the two augmentation coordinates; compatibility with geometric restriction
on the intersection of the standard opens is a separate assertion. -/
theorem symmetricQuotientFraction_changeLift
    (C : SymmetricQuotientChart R M) (s' : M)
    (hs' : C.quotient s' = 1) (k : LinearMap.ker C.quotient) :
    C.symmetricQuotientFractionClass k =
      (({ C with generatorLift := s', generatorLift_spec := hs' } :
        SymmetricQuotientChart R M).symmetricQuotientFractionClass k) := by
  apply congrArg (SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient)).toCotangent
  apply Subtype.ext
  exact (C.standardOpenEquiv_fraction C.generatorLift C.generatorLift_spec k).trans
    (({ C with generatorLift := s', generatorLift_spec := hs' } :
      SymmetricQuotientChart R M).standardOpenEquiv_fraction s' hs' k).symm

end SymmetricQuotientChart

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- The canonical linear map from the quotient kernel to the augmentation cotangent module. -/
def symmetricQuotientKernelToConormal (C : SymmetricQuotientChart R M) :
    LinearMap.ker C.quotient →ₗ[R]
      (SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient)).Cotangent :=
  SymmetricAlgebra.toAugmentationCotangent R (LinearMap.ker C.quotient)

/-- The canonical kernel-to-augmentation-cotangent map is bijective. -/
theorem symmetricQuotientKernelToConormal_isIso
    (C : SymmetricQuotientChart R M) :
    Function.Bijective (symmetricQuotientKernelToConormal C) :=
  SymmetricAlgebra.toAugmentationCotangent_bijective R (LinearMap.ker C.quotient)

/-- The canonical kernel map is the conormal class represented by the actual homogeneous
fraction `k / s` in standard-open coordinates. -/
theorem symmetricQuotientKernelToConormal_natural
    (C : SymmetricQuotientChart R M) (k : LinearMap.ker C.quotient) :
    symmetricQuotientKernelToConormal C k =
      C.symmetricQuotientFractionClass k := by
  change (SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient)).toCotangent
      (SymmetricAlgebra.toAugmentationIdeal R (LinearMap.ker C.quotient) k) = _
  apply congrArg (SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient)).toCotangent
  apply Subtype.ext
  exact (C.standardOpenEquiv_fraction C.generatorLift C.generatorLift_spec k).symm

end AlgebraicGeometry.Proj
