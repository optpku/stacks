/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.K0.Support
public import ReasLib.AlgebraicGeometry.Scheme.K0.Support.Ring
public import ReasLib.CategoryTheory.Pretriangulated.K0.Universal
public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses
public import stacks_project.Chap42.Definition_42_50_3_RationalBivariant
public import stacks_project.Chap42.Lemma_42_47_11_IntersectionProduct
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Localized Chern character on supported-perfect `K₀`

The vanishing-mode localized Chern character of Definition 42.50.3 lifts additively
through `K₀(D_{Z,perf}(O_X))`, and is multiplicative for derived tensor product
against self-intersection convolution on `∏_{i≥0} Aⁱ(Z ⟶ X) ⊗ ℚ`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open AlgebraicGeometry.LocalizedChern
open AlgebraicGeometry.BivariantClass.Nonnegative

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.K0WithSupport

variable {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
variable {X : Over S} [LocallyOfFiniteType X.hom] {Z : Scheme.{u}}
variable (i : Z ⟶ X.left) [IsClosedImmersion i]

/-- Quasi-compactness of every irreducible component of `X`, together with support on `Z`,
produces a vanishing-mode localized-Chern situation. -/
theorem characterSituation
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    Situation S δ X i E.obj 0 .vanishing := sorry

/-- The localized Chern character of a supported perfect complex, as a completed rational
bivariant class of `Z ⟶ X`. -/
def chernCharacterValue
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  character i classes E.obj (characterSituation δ i hqc E).perfect
    (characterSituation δ i hqc E).offCenter
    (characterSituation δ i hqc E).finiteness

/-- A coefficient of the generator-level localized Chern character is the corresponding
localized character component. -/
theorem chernCharacterValue_apply
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) (p : ℕ) :
    chernCharacterValue δ i hqc classes E p =
      character i classes E.obj (characterSituation δ i hqc E).perfect
        (characterSituation δ i hqc E).offCenter
        (characterSituation δ i hqc E).finiteness p := sorry

/-- Localized Chern characters of supported perfect complexes add on distinguished
triangles. -/
theorem chernCharacterValue_distinguished
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (T : Triangle (RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)))
    (hT : T ∈ distTriang (RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base))) :
    chernCharacterValue δ i hqc classes T.obj₂ =
      chernCharacterValue δ i hqc classes T.obj₁ +
        chernCharacterValue δ i hqc classes T.obj₃ := sorry

/-- The additive localized Chern character on supported-perfect `K₀`. -/
def chernCharacter
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    K0WithSupport X.left (Set.range i.base) →+
      RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  TriangulatedK0.liftOfDistinguished (chernCharacterValue δ i hqc classes)
    (chernCharacterValue_distinguished δ i hqc classes)

/-- The bundled localized Chern character sends a supported-perfect generator to its
localized character. -/
theorem chernCharacter_of
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (E : RingedSpace.ModuleDerived.PerfectSupportedOn (Set.range i.base)) :
    chernCharacter δ i hqc classes (TriangulatedK0.of E) =
      chernCharacterValue δ i hqc classes E := sorry

/-- The zero class maps to the zero completed rational bivariant class. -/
theorem chernCharacter_zero
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) :
    chernCharacter δ i hqc classes 0 = 0 := sorry

/-- The self-square of a closed immersion is cartesian. -/
theorem selfIntersectionPullback : IsPullback (𝟙 Z) (𝟙 Z) i i := sorry

/-- The integral self-intersection product of two homogeneous bivariant classes of a
closed immersion. -/
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
          (selfIntersectionPullback i) (Category.id_comp _) c d) := sorry

/-- Linear extension of `selfIntersectionMul` in the second homogeneous factor. -/
def selfIntersectionMulLinear (p q : ℕ)
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)) :
    BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ) →ₗ[ℤ]
      BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) ((p + q : ℕ) : ℤ) where
  toFun d := selfIntersectionMul δ i c d
  map_add' := sorry
  map_smul' := sorry

/-- `selfIntersectionMulLinear` evaluates as `selfIntersectionMul`. -/
theorem selfIntersectionMulLinear_apply (p q : ℕ)
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ))
    (d : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ)) :
    selfIntersectionMulLinear δ i p q c d = selfIntersectionMul δ i c d := sorry

/-- Rational homogeneous self-intersection of two completed bivariant degrees. -/
def intersectionConvolutionHomogeneous (p q : ℕ)
    (x : RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p)
    (y : RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) q) :
    RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p + q) :=
  let f := (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)
  let φ : BivariantClass δ f (p : ℤ) →ₗ[ℤ]
      ℚ →ₗ[ℤ] RationalDegree δ f (p + q) :=
    { toFun := fun c =>
        { toFun := fun qv =>
            let mulQ : ℚ →ₗ[ℤ] ℚ :=
              { toFun := fun rv => qv * rv, map_add' := sorry, map_smul' := sorry }
            (TensorProduct.map (selfIntersectionMulLinear δ i p q c) mulQ :
                RationalDegree δ f q →ₗ[ℤ] RationalDegree δ f (p + q)) y
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }
  TensorProduct.lift φ x

/-- Homogeneous self-intersection of pure tensors multiplies the integral classes and the
rational scalars. -/
theorem intersectionConvolutionHomogeneous_tmul (p q : ℕ)
    (c : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (p : ℤ)) (qv : ℚ)
    (d : BivariantClass δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) (q : ℤ)) (rv : ℚ) :
    intersectionConvolutionHomogeneous δ i p q (TensorProduct.tmul ℤ c qv)
        (TensorProduct.tmul ℤ d rv) =
      TensorProduct.tmul ℤ (selfIntersectionMul δ i c d) (qv * rv) := sorry

/-- Transport a rational homogeneous class along an equality of degrees. -/
def castRationalDegree {p q : ℕ} (h : p = q)
    (x : RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p) :
    RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) q :=
  Eq.mp (congrArg (RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) h) x

/-- Transport along reflexivity leaves a rational homogeneous class unchanged. -/
theorem castRationalDegree_rfl {p : ℕ}
    (x : RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) p) :
    castRationalDegree δ i rfl x = x := sorry

/-- The homogeneous self-intersection indexed by an antidiagonal element, transported to
its specified total degree. -/
def intersectionConvolutionTerm
    (a b : RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) :
    RationalDegree δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) n :=
  castRationalDegree δ i (Finset.mem_antidiagonal.mp ij.property)
    (intersectionConvolutionHomogeneous δ i ij.1.1 ij.1.2 (a ij.1.1) (b ij.1.2))

/-- An antidiagonal convolution term is transported homogeneous self-intersection. -/
theorem intersectionConvolutionTerm_apply
    (a b : RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) :
    intersectionConvolutionTerm δ i a b n ij =
      castRationalDegree δ i (Finset.mem_antidiagonal.mp ij.property)
        (intersectionConvolutionHomogeneous δ i ij.1.1 ij.1.2 (a ij.1.1) (b ij.1.2)) :=
  sorry

/-- Finite Cauchy convolution of completed rational bivariant classes against the
self-intersection product of a closed immersion. -/
def intersectionConvolution
    (a b : RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) :
    RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X) :=
  fun n ↦ (Finset.antidiagonal n).attach.sum (intersectionConvolutionTerm δ i a b n)

/-- Convolution is coefficientwise finite Cauchy self-intersection. -/
theorem intersectionConvolution_apply
    (a b : RationalCompletion δ (Over.homMk i : Over.mk (i ≫ X.hom) ⟶ X)) (n : ℕ) :
    intersectionConvolution δ i a b n =
      (Finset.antidiagonal n).attach.sum (intersectionConvolutionTerm δ i a b n) :=
  sorry

/-- Derived-tensor multiplication on supported-perfect `K₀` is sent to self-intersection
convolution of localized Chern characters. -/
theorem chernCharacter_mul
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom)
    (a b : K0WithSupport X.left (Set.range i.base)) :
    chernCharacter δ i hqc classes (a * b) =
      intersectionConvolution δ i (chernCharacter δ i hqc classes a)
        (chernCharacter δ i hqc classes b) := sorry

/-- If `X` is quasi-compact, the localized Chern character of a supported-perfect class
has only finitely many nonzero homogeneous components. -/
theorem chernCharacter_finiteSupport
    (hqc : ∀ C : irreducibleComponents X.left, IsCompact (C : Set X.left))
    (classes : ChernClass.Theory δ X.hom) (hX : CompactSpace X.left)
    (a : K0WithSupport X.left (Set.range i.base)) :
    {p : ℕ | chernCharacter δ i hqc classes a p ≠ 0}.Finite := sorry

end AlgebraicGeometry.Scheme.K0WithSupport
