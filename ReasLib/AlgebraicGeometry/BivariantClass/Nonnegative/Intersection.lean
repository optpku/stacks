module

public import ReasLib.AlgebraicGeometry.BivariantClass.Intersection
public import ReasLib.AlgebraicGeometry.BivariantClass.Nonnegative.Rational
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Data.Finset.NatAntidiagonal

public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Nonnegative.Rational

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]

/-- The self-square of a closed immersion is cartesian. -/
theorem selfIntersectionPullback : IsPullback (𝟙 Z) (𝟙 Z) i i := sorry

/-- The integral self-intersection product of two homogeneous bivariant classes of a
closed immersion. -/
@[expose]
def selfIntersectionMul {p q : ℕ}
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (d : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ)) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ((p + q : ℕ) : ℤ) :=
  castGrading δ (Nat.cast_add p q).symm
    (BivariantClass.intersectionMul δ
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
      (𝟙 (Over.mk (i ≫ X.hom))) (𝟙 (Over.mk (i ≫ X.hom)))
      (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
      (selfIntersectionPullback i) (Category.id_comp _) c d)

/-- `selfIntersectionMul` is grading transport of self-intersection `intersectionMul`. -/
theorem selfIntersectionMul_apply {p q : ℕ}
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (d : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ)) :
    selfIntersectionMul δ i c d =
      castGrading δ (Nat.cast_add p q).symm
        (BivariantClass.intersectionMul δ
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
          (𝟙 (Over.mk (i ≫ X.hom))) (𝟙 (Over.mk (i ≫ X.hom)))
          (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
          (selfIntersectionPullback i) (Category.id_comp _) c d) := rfl

/-- Self-intersection is additive in its first integral factor. -/
theorem selfIntersectionMul_add_left {p q : ℕ}
    (c c' : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (d : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ)) :
    selfIntersectionMul δ i (pointwiseAdd δ _ _ c c') d =
      pointwiseAdd δ _ _ (selfIntersectionMul δ i c d) (selfIntersectionMul δ i c' d) := sorry

/-- Self-intersection is additive in its second integral factor. -/
theorem selfIntersectionMul_add_right {p q : ℕ}
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (d d' : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ)) :
    selfIntersectionMul δ i c (pointwiseAdd δ _ _ d d') =
      pointwiseAdd δ _ _ (selfIntersectionMul δ i c d) (selfIntersectionMul δ i c d') := sorry

/-- The integral self-intersection product as an integer-bilinear map. -/
private def selfIntersectionMulLinear (p q : ℕ) :=
  let f := (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
  let A := BivariantClass δ f (p : ℤ)
  let B := BivariantClass δ f (q : ℤ)
  let C := BivariantClass δ f ((p + q : ℕ) : ℤ)
  let GA := pointwiseAddCommGroup δ f (p : ℤ)
  let GB := pointwiseAddCommGroup δ f (q : ℤ)
  let GC := pointwiseAddCommGroup δ f ((p + q : ℕ) : ℤ)
  let L := @LinearMap ℤ ℤ inferInstance inferInstance (RingHom.id ℤ) B C
    GB.toAddCommMonoid GC.toAddCommMonoid
    (@AddCommGroup.toIntModule B GB) (@AddCommGroup.toIntModule C GC)
  let inner : A → L := fun c ↦
    @AddMonoidHom.toIntLinearMap B C GB GC
      (@AddMonoidHom.mk' B C GC.toAddGroup GB.toAddZeroClass
        (selfIntersectionMul δ i c) (selfIntersectionMul_add_right δ i c))
  @AddMonoidHom.toIntLinearMap A L GA inferInstance
    (@AddMonoidHom.mk' A L inferInstance GA.toAddZeroClass inner (by
      intro c c'
      apply LinearMap.ext
      intro d
      exact selfIntersectionMul_add_left δ i c c' d))

/-- Rational homogeneous self-intersection of two bivariant degrees. -/
def intersectionConvolutionHomogeneous (p q : ℕ)
    (x : Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p)
    (y : Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) q) :
    Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p + q) :=
  let f := (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
  @TensorProduct.map₂ ℤ ℤ ℤ inferInstance inferInstance inferInstance
    (RingHom.id ℤ) (RingHom.id ℤ)
    (BivariantClass δ f (p : ℤ)) ℚ
    (BivariantClass δ f (q : ℤ)) (BivariantClass δ f ((p + q : ℕ) : ℤ)) ℚ ℚ
    (pointwiseAddCommGroup δ f (p : ℤ)).toAddCommMonoid inferInstance
    (pointwiseAddCommGroup δ f (q : ℤ)).toAddCommMonoid inferInstance
    (pointwiseAddCommGroup δ f ((p + q : ℕ) : ℤ)).toAddCommMonoid inferInstance
    (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (p : ℤ))) inferInstance
    (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f (q : ℤ))) inferInstance
    (@AddCommGroup.toIntModule _ (pointwiseAddCommGroup δ f ((p + q : ℕ) : ℤ))) inferInstance
    (selfIntersectionMulLinear δ i p q) (LinearMap.mul ℤ ℚ) x y

/-- Homogeneous self-intersection of pure tensors multiplies the integral classes and the
rational scalars. -/
theorem intersectionConvolutionHomogeneous_tmul (p q : ℕ)
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)) (qv : ℚ)
    (d : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ)) (rv : ℚ) :
    intersectionConvolutionHomogeneous δ i p q (tensor δ _ p c qv)
        (tensor δ _ q d rv) =
      tensor δ _ (p + q) (selfIntersectionMul δ i c d) (qv * rv) := sorry

/-- Transport a rational homogeneous class along an equality of degrees. -/
@[expose]
def castRationalDegree {p q : ℕ} (h : p = q)
    (x : Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p) :
    Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) q :=
  Eq.mp (congrArg (Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) h) x

/-- Transport along reflexivity leaves a rational homogeneous class unchanged. -/
theorem castRationalDegree_rfl {p : ℕ}
    (x : Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p) :
    castRationalDegree δ i rfl x = x := rfl

/-- The homogeneous self-intersection indexed by an antidiagonal element, transported to
its specified total degree. -/
@[expose]
def intersectionConvolutionTerm
    (a b : Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) :
    Degree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) n :=
  castRationalDegree δ i (Finset.mem_antidiagonal.mp ij.property)
    (intersectionConvolutionHomogeneous δ i ij.1.1 ij.1.2 (a ij.1.1) (b ij.1.2))

/-- An antidiagonal convolution term is transported homogeneous self-intersection. -/
theorem intersectionConvolutionTerm_apply
    (a b : Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) :
    intersectionConvolutionTerm δ i a b n ij =
      castRationalDegree δ i (Finset.mem_antidiagonal.mp ij.property)
        (intersectionConvolutionHomogeneous δ i ij.1.1 ij.1.2 (a ij.1.1) (b ij.1.2)) :=
  rfl

/-- Finite Cauchy convolution of completed rational bivariant classes against the
self-intersection product of a closed immersion. -/
@[expose]
def intersectionConvolution
    (a b : Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) :
    Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  fun n ↦ (Finset.antidiagonal n).attach.sum (intersectionConvolutionTerm δ i a b n)

/-- Convolution is coefficientwise finite Cauchy self-intersection. -/
theorem intersectionConvolution_apply
    (a b : Completion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (n : ℕ) :
    intersectionConvolution δ i a b n =
      (Finset.antidiagonal n).attach.sum (intersectionConvolutionTerm δ i a b n) :=
  rfl

end AlgebraicGeometry.BivariantClass.Nonnegative.Rational
