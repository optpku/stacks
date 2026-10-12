/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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
      AlgHom.id R (SymmetricAlgebra R M) := sorry

/-- A homogeneous element decomposes into its given direct-sum component. -/
theorem gradedAlgebraDecompose_leftInv (n : ℕ) (x : grading R M n) :
    gradedAlgebraDecompose x = DirectSum.of (fun d ↦ ↥(grading R M d)) n x := sorry

/-- The powers-of-degree-one decomposition gives the canonical grading on a symmetric algebra. -/
noncomputable instance gradingGradedAlgebra : GradedAlgebra (grading R M) :=
  GradedAlgebra.ofAlgHom (grading R M) gradedAlgebraDecompose
    gradedAlgebraDecompose_rightInv gradedAlgebraDecompose_leftInv

/-- Symmetric-algebra generators are homogeneous of degree one. -/
theorem generator_mem_degreeOne (x : M) :
    SymmetricAlgebra.ι R M x ∈ grading R M 1 := sorry

/-- Projection onto the kernel determined by the chosen splitting of the quotient. -/
def kernelProjection (C : SymmetricQuotientChart R M) :
    M →ₗ[R] LinearMap.ker C.quotient where
  toFun x := ⟨x - C.quotient x • C.generatorLift, by
    simp [C.generatorLift_spec]⟩
  map_add' := sorry
  map_smul' := sorry

/-- The split coordinates recover a vector from its kernel and quotient components. -/
theorem kernelProjection_add_quotient_smul (C : SymmetricQuotientChart R M) (x : M) :
    (C.kernelProjection x : M) + C.quotient x • C.generatorLift = x := sorry

/-- Evaluating the quotient coordinate at `1` and retaining the kernel coordinates. -/
def evaluation (C : SymmetricQuotientChart R M) :
    SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R (LinearMap.ker C.quotient) :=
  SymmetricAlgebra.lift
    { toFun := fun x ↦
        SymmetricAlgebra.ι R (LinearMap.ker C.quotient) (C.kernelProjection x) +
          algebraMap R (SymmetricAlgebra R (LinearMap.ker C.quotient)) (C.quotient x)
      map_add' := sorry
      map_smul' := sorry }

/-- The homogeneous element inverted by the chart. -/
def denominatorAt (_ : SymmetricQuotientChart R M) (s : M) :
    SymmetricAlgebra R M :=
  SymmetricAlgebra.ι R M s

/-- The homogeneous element inverted by the chosen quotient splitting. -/
def denominator (C : SymmetricQuotientChart R M) : SymmetricAlgebra R M :=
  C.denominatorAt C.generatorLift

/-- The degree-zero homogeneous localization for a specified lift of the quotient unit. -/
abbrev awayAt (C : SymmetricQuotientChart R M) (s : M) :=
  HomogeneousLocalization.Away (grading R M) (C.denominatorAt s)

/-- The degree-zero homogeneous localization for the chosen lift. -/
abbrev away (C : SymmetricQuotientChart R M) := C.awayAt C.generatorLift

/-- Evaluation sends every lift of the quotient unit to `1`. -/
theorem evaluation_denominatorAt (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) : C.evaluation (C.denominatorAt s) = 1 := sorry

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
  Localization.awayLift C.evaluation.toRingHom (C.denominatorAt s) (by
    change IsUnit (C.evaluation (C.denominatorAt s))
    rw [C.evaluation_denominatorAt s hs]
    exact isUnit_one)

/-- The forward coordinate map from the standard open to the symmetric algebra of the kernel. -/
noncomputable def standardOpenHom (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) :
    C.awayAt s →ₐ[R] SymmetricAlgebra R (LinearMap.ker C.quotient) where
  __ := (C.awayEvaluation s hs).comp (C.awayValRingHom s)
  commutes' := sorry

/-- The homogeneous fraction `k / s` associated to a kernel element. -/
def fractionLinear (C : SymmetricQuotientChart R M) (s : M) :
    LinearMap.ker C.quotient →ₗ[R] C.awayAt s where
  toFun k := HomogeneousLocalization.Away.mk (grading R M)
    (generator_mem_degreeOne s) 1 (SymmetricAlgebra.ι R M k.1)
      (generator_mem_degreeOne k.1)
  map_add' := sorry
  map_smul' := sorry

/-- The inverse coordinate map, obtained from the universal property of the symmetric algebra. -/
def standardOpenInv (C : SymmetricQuotientChart R M) (s : M) :
    SymmetricAlgebra R (LinearMap.ker C.quotient) →ₐ[R] C.awayAt s :=
  SymmetricAlgebra.lift (C.fractionLinear s)

/-- The forward and inverse standard-open coordinate maps are inverse. -/
theorem standardOpenMaps_inverse (C : SymmetricQuotientChart R M)
    (s : M) (hs : C.quotient s = 1) :
    Function.LeftInverse (C.standardOpenInv s) (C.standardOpenHom s hs) ∧
      Function.LeftInverse (C.standardOpenHom s hs) (C.standardOpenInv s) := sorry

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
      SymmetricAlgebra.ι R (LinearMap.ker C.quotient) k := sorry

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
      SymmetricAlgebra.augmentationIdeal R (LinearMap.ker C.quotient) := sorry

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

/-- Replacing the lift of the quotient unit does not change the conormal class. -/
theorem symmetricQuotientFraction_changeLift
    (C : SymmetricQuotientChart R M) (s' : M)
    (hs' : C.quotient s' = 1) (k : LinearMap.ker C.quotient) :
    C.symmetricQuotientFractionClass k =
      (({ C with generatorLift := s', generatorLift_spec := hs' } :
        SymmetricQuotientChart R M).symmetricQuotientFractionClass k) := sorry

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
    Function.Bijective (symmetricQuotientKernelToConormal C) := sorry

/-- The canonical kernel map is the conormal class represented by the actual homogeneous
fraction `k / s` in standard-open coordinates. -/
theorem symmetricQuotientKernelToConormal_natural
    (C : SymmetricQuotientChart R M) (k : LinearMap.ker C.quotient) :
    symmetricQuotientKernelToConormal C k =
      C.symmetricQuotientFractionClass k := sorry

end AlgebraicGeometry.Proj
