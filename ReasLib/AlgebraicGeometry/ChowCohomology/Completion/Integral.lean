module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Theory
public import Mathlib.Algebra.Ring.MinimalAxioms
public import Mathlib.GroupTheory.Submonoid.Center
public import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# The completed nonnegative Chow-cohomology ring

This module equips the product of the integral nonnegative homogeneous
Chow-cohomology groups with finite Cauchy-convolution multiplication and
constructs formal inverses of series whose constant coefficient is one.
-/

@[expose] public section

open CategoryTheory
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChowCohomology.Nonnegative

variable {S X : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
variable [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]

/-- The completed integral nonnegative Chow-cohomology carrier. -/
abbrev Completion : Type (u + 1) :=
  ∀ i : ℕ, degree δ p i

/-- `Completion` is the dependent product of all nonnegative Chow-cohomology degrees. -/
theorem completion_def : Completion δ p = (∀ i : ℕ, degree δ p i) := sorry

namespace Completion

/-- Two completed classes are equal when all coefficients agree. -/
@[ext]
theorem ext {a b : Completion δ p} (h : ∀ i, a i = b i) : a = b := sorry

/-- Transport an integral homogeneous class along an equality of degrees. -/
def castDegree {i j : ℕ} (h : i = j) (x : degree δ p i) : degree δ p j :=
  Eq.mp (congrArg (degree δ p) h) x

/-- Transport along reflexivity leaves an integral homogeneous class unchanged. -/
theorem castDegree_rfl {i : ℕ} (x : degree δ p i) :
    castDegree δ p rfl x = x := sorry

/-- The convolution unit is the degree-zero identity class. -/
def one : Completion δ p
  | 0 => ChowCohomology.one δ p
  | _ + 1 => 0

/-- The degree-zero coefficient of the convolution unit. -/
theorem one_apply_zero : one δ p 0 = ChowCohomology.one δ p := sorry

/-- Every positive-degree coefficient of the convolution unit vanishes. -/
theorem one_apply_succ (n : ℕ) : one δ p (n + 1) = 0 := sorry

/-- The homogeneous product indexed by an antidiagonal element, transported to its
specified total degree. -/
def antidiagonalMul (a b : Completion δ p) (n : ℕ)
    (ij : {ij : ℕ × ℕ // ij ∈ Finset.antidiagonal n}) : degree δ p n :=
  castDegree δ p (Finset.mem_antidiagonal.mp ij.property)
    (Nonnegative.mul δ p (a ij.1.1) (b ij.1.2))

/-- Finite Cauchy convolution on completed integral Chow-cohomology classes. -/
def mul (a b : Completion δ p) : Completion δ p :=
  fun n ↦ (Finset.antidiagonal n).attach.sum (antidiagonalMul δ p a b n)

/-- Multiplication is coefficientwise finite Cauchy convolution. -/
theorem mul_apply (a b : Completion δ p) (n : ℕ) :
    mul δ p a b n =
      (Finset.antidiagonal n).attach.sum (antidiagonalMul δ p a b n) := sorry

/-- The canonical unit on completed integral nonnegative Chow cohomology. -/
noncomputable instance instOne : One (Completion δ p) := ⟨one δ p⟩

/-- The canonical convolution multiplication on completed integral nonnegative Chow cohomology. -/
noncomputable instance instMul : Mul (Completion δ p) := ⟨mul δ p⟩

/-- Convolution multiplication is associative. -/
theorem mul_assoc_axiom (a b c : Completion δ p) : a * b * c = a * (b * c) := sorry

/-- The degree-zero identity is a left unit for convolution. -/
theorem one_mul_axiom (a : Completion δ p) : 1 * a = a := sorry

/-- The degree-zero identity is a right unit for convolution. -/
theorem mul_one_axiom (a : Completion δ p) : a * 1 = a := sorry

/-- Convolution distributes over addition in the right variable. -/
theorem mul_add_axiom (a b c : Completion δ p) :
    a * (b + c) = a * b + a * c := sorry

/-- Convolution distributes over addition in the left variable. -/
theorem add_mul_axiom (a b c : Completion δ p) :
    (a + b) * c = a * c + b * c := sorry

/-- The canonical ring structure on completed integral nonnegative Chow cohomology. -/
noncomputable instance instRing : Ring (Completion δ p) :=
  Ring.ofMinimalAxioms add_assoc zero_add neg_add_cancel
    (mul_assoc_axiom δ p) (one_mul_axiom δ p) (mul_one_axiom δ p)
      (mul_add_axiom δ p) (add_mul_axiom δ p)

/-- Regard a completed class as a formal power series in the finite-support
nonnegative Chow-cohomology ring. -/
def toPowerSeries (a : Completion δ p) : PowerSeries (Nonnegative.ring δ p) :=
  PowerSeries.mk fun i ↦ ChernClass.homogeneous δ p i (a i)

/-- The coefficient of `toPowerSeries a` is the homogeneous embedding of `a i`. -/
theorem toPowerSeries_coeff (a : Completion δ p) (i : ℕ) :
    PowerSeries.coeff i (toPowerSeries δ p a) =
      ChernClass.homogeneous δ p i (a i) := sorry

/-- The formal inverse of a completed class, obtained coefficientwise from the
power-series inverse with unit constant term. -/
def formalInverse (a : Completion δ p) : Completion δ p :=
  fun i ↦ DirectSum.component ℤ ℕ (degree δ p) i
    (PowerSeries.coeff i (PowerSeries.invOfUnit (toPowerSeries δ p a) 1))

/-- A formal-inverse coefficient is the matching homogeneous projection of the
power-series inverse. -/
theorem formalInverse_apply (a : Completion δ p) (i : ℕ) :
    formalInverse δ p a i = DirectSum.component ℤ ℕ (degree δ p) i
      (PowerSeries.coeff i (PowerSeries.invOfUnit (toPowerSeries δ p a) 1)) := sorry

/-- A completed class with unit constant coefficient multiplies its formal inverse to one. -/
theorem mul_formalInverse (a : Completion δ p)
    (ha : a 0 = ChowCohomology.one δ p) : a * formalInverse δ p a = 1 := sorry

/-- The formal inverse of a completed class with unit constant coefficient multiplies it to one. -/
theorem formalInverse_mul (a : Completion δ p)
    (ha : a 0 = ChowCohomology.one δ p) : formalInverse δ p a * a = 1 := sorry

/-- The formal inverse of a central completed class is central. -/
theorem formalInverse_mem_center (a : Completion δ p)
    (ha : a 0 = ChowCohomology.one δ p) (hcentral : a ∈ Set.center (Completion δ p)) :
    formalInverse δ p a ∈ Set.center (Completion δ p) := sorry

/-- Package a central completed class with constant coefficient one as a unit of the center. -/
def unitOf (a : Completion δ p) (ha : a 0 = ChowCohomology.one δ p)
    (hcentral : a ∈ Set.center (Completion δ p)) :
    (Submonoid.center (Completion δ p))ˣ where
  val := ⟨a, hcentral⟩
  inv := ⟨formalInverse δ p a, formalInverse_mem_center δ p a ha hcentral⟩
  val_inv := Subtype.ext (mul_formalInverse δ p a ha)
  inv_val := Subtype.ext (formalInverse_mul δ p a ha)

/-- The value of `unitOf` is the completed class supplied to it. -/
theorem unitOf_val (a : Completion δ p) (ha : a 0 = ChowCohomology.one δ p)
    (hcentral : a ∈ Set.center (Completion δ p)) :
    (unitOf δ p a ha hcentral).val.val = a := sorry

/-- The inverse value of `unitOf` is the named formal inverse. -/
theorem unitOf_inv (a : Completion δ p) (ha : a 0 = ChowCohomology.one δ p)
    (hcentral : a ∈ Set.center (Completion δ p)) :
    (unitOf δ p a ha hcentral).inv.val = formalInverse δ p a := sorry

end Completion

end AlgebraicGeometry.ChowCohomology.Nonnegative
