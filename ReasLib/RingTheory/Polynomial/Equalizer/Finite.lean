module

public import ReasLib.RingTheory.Polynomial.Equalizer
public import Mathlib.RingTheory.FiniteType
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.CrossRefAttribute
import ReasLib.RingTheory.FiniteType.ArtinTate

/-!
# Finite polynomial evaluation equalizers

@stack 00F1
@stack 00JG

For two points whose difference is a unit in a commutative ring, their polynomial-evaluation
equalizer has a two-generator finite extension. The equal-endpoint algebra is the specialization
at `0` and `1`.
-/

@[expose] public section

noncomputable section

namespace Polynomial

universe u

namespace EvalEqualizer

variable {R : Type u} [CommRing R]

/-- The monic quadratic vanishing at `x` and `y`. -/
@[stacks 00JG "two-point vanishing polynomial"]
def vanishing (x y : R) : R[X] :=
  (X - C x) * (X - C y)

@[simp]
theorem vanishing_eval_left (x y : R) :
    (vanishing x y).eval x = 0 := by
  simp [vanishing]

@[simp]
theorem vanishing_eval_right (x y : R) :
    (vanishing x y).eval y = 0 := by
  simp [vanishing]

/-- The vanishing polynomial is symmetric in its two roots. -/
theorem vanishing_comm (x y : R) : vanishing x y = vanishing y x := by
  simp only [vanishing, mul_comm]

section Ring

/-- If the difference of two points is a unit, equality at those points forces divisibility by
their vanishing quadratic after subtracting the common constant value. -/
@[stacks 00JG "two-point vanishing divisibility"]
theorem vanishing_dvd_sub_C_eval (x y : R) (hxy : IsUnit (x - y))
    (f : R[X]) (hf : f.eval x = f.eval y) :
    vanishing x y ∣ f - C (f.eval x) := by
  change (X - C x) * (X - C y) ∣ f - C (f.eval x)
  apply (isCoprime_X_sub_C_of_isUnit_sub hxy).mul_dvd
  · exact X_sub_C_dvd_sub_C_eval
  · rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_C, hf, sub_self]

/-- If two points differ by a unit, a polynomial taking the same value there is its common
constant value plus a multiple of their vanishing quadratic. -/
@[stacks 00JG "two-point vanishing decomposition"]
theorem exists_eq_C_add_vanishing_mul (x y : R) (hxy : IsUnit (x - y))
    (f : R[X]) (hf : f.eval x = f.eval y) :
    ∃ q : R[X], f = C (f.eval x) + vanishing x y * q := by
  rcases vanishing_dvd_sub_C_eval x y hxy f hf with ⟨q, hq⟩
  exact ⟨q, eq_add_of_sub_eq' hq⟩

/-- The two-generator presentation of the polynomial ring over an evaluation equalizer. -/
@[stacks 00JG "two-generator presentation of a polynomial evaluation equalizer"]
def generatorMap (x y : R) :
    (evalEqualizer (R := R) x y × evalEqualizer (R := R) x y) →ₗ[evalEqualizer (R := R) x y] R[X] :=
  LinearMap.coprod
    (LinearMap.toSpanSingleton (evalEqualizer (R := R) x y) R[X] 1)
    (LinearMap.toSpanSingleton (evalEqualizer (R := R) x y) R[X] (X - C x))

/-- The generator map sends `(r, s)` to `r + s (X - x)`. -/
@[simp]
theorem generatorMap_apply (x y : R)
    (p : evalEqualizer (R := R) x y × evalEqualizer (R := R) x y) :
    generatorMap x y p = (p.1 : R[X]) + (p.2 : R[X]) * (X - C x) := by
  simp [generatorMap, Algebra.smul_def]

/-- Unit-separated evaluation points give a surjective two-generator presentation. -/
@[stacks 00JG "surjective two-generator polynomial presentation"]
theorem generatorMap_surjective (x y : R) (hxy : IsUnit (x - y)) :
    Function.Surjective (generatorMap x y) := by
  intro f
  -- These coordinates use the inverse supplied by `hxy`; keeping them proof-local avoids a
  -- proof-indexed public interpolation object.
  have hyx : IsUnit (y - x) := IsUnit.sub_iff.mp hxy
  let c : R := (f.eval y - f.eval x) * (↑hyx.unit⁻¹ : R)
  let p : R[X] := f - C c * (X - C x)
  have hp : p ∈ evalEqualizer (R := R) x y := by
    rw [mem_evalEqualizer]
    change p.eval x = p.eval y
    simp only [p, eval_sub, eval_mul, eval_C, eval_X, sub_self, mul_zero, sub_zero]
    dsimp [c]
    rw [mul_assoc, hyx.val_inv_mul, mul_one, sub_sub_cancel]
  refine ⟨(⟨p, hp⟩, algebraMap R (evalEqualizer (R := R) x y) c), ?_⟩
  rw [generatorMap_apply]
  change p + C c * (X - C x) = f
  simp [p]

/-- The polynomial ring is finite over the equalizer of unit-separated evaluations. -/
@[stacks 00JG "finite polynomial evaluation equalizer extension"]
theorem moduleFinite (x y : R) (hxy : IsUnit (x - y)) :
    Module.Finite (evalEqualizer (R := R) x y) R[X] :=
  Module.Finite.of_surjective (generatorMap x y) (generatorMap_surjective x y hxy)

end Ring

section Field

variable {K : Type u} [Field K]

/-- Equality at two distinct points forces divisibility by their vanishing quadratic after
subtracting the common constant value. -/
theorem vanishing_dvd_sub_C_eval_of_ne (x y : K) (hxy : x ≠ y) (f : K[X])
    (hf : f.eval x = f.eval y) :
    vanishing x y ∣ f - C (f.eval x) :=
  vanishing_dvd_sub_C_eval x y (sub_ne_zero.mpr hxy).isUnit f hf

/-- A polynomial taking the same value at two distinct points is its common constant value plus
a multiple of the monic quadratic vanishing at those points. -/
theorem exists_eq_C_add_vanishing_mul_of_ne (x y : K) (hxy : x ≠ y) (f : K[X])
    (hf : f.eval x = f.eval y) :
    ∃ q : K[X], f = C (f.eval x) + vanishing x y * q :=
  exists_eq_C_add_vanishing_mul x y (sub_ne_zero.mpr hxy).isUnit f hf

/-- The slope of a polynomial between two points. -/
def slope (x y : K) (f : K[X]) : K :=
  (f.eval y - f.eval x) / (y - x)

/-- Subtract the affine interpolation term based at `x`. -/
def remainder (x y : K) (f : K[X]) : K[X] :=
  f - C (slope x y f) * (X - C x)

/-- The interpolation remainder takes the same value at the two endpoints. -/
theorem remainder_mem (x y : K) (hxy : x ≠ y) (f : K[X]) :
    remainder x y f ∈ evalEqualizer (R := K) x y := by
  rw [mem_evalEqualizer]
  change (remainder x y f).eval x = (remainder x y f).eval y
  simp only [remainder, eval_sub, eval_mul, eval_C, eval_X, sub_self, mul_zero, sub_zero,
    slope]
  rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hxy.symm)]
  exact (sub_sub_cancel _ _).symm

/-- The interpolation remainder together with `X - x` reconstructs the polynomial. -/
theorem remainder_add_slope_mul (x y : K) (f : K[X]) :
    remainder x y f + C (slope x y f) * (X - C x) = f := by
  simp [remainder]

/-- The interpolation remainder as an element of the evaluation equalizer. -/
def remainderElement (x y : K) (hxy : x ≠ y) (f : K[X]) : evalEqualizer (R := K) x y :=
  ⟨remainder x y f, remainder_mem x y hxy f⟩

end Field

end EvalEqualizer

namespace EqualEndpoint

section Semiring

variable {R : Type u} [CommSemiring R]

/-- The coefficient semiring is finite over the equal-endpoint algebra via common evaluation. -/
@[stacks 00JG "finite common-endpoint module"]
noncomputable instance endpointModuleFinite :
    Module.Finite (equalEndpoint R) R := by
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨{(1 : R)}, Set.finite_singleton _, ?_⟩
  rw [Submodule.span_singleton_eq_top_iff]
  intro a
  refine ⟨algebraMap R (equalEndpoint R) a, ?_⟩
  simp [Algebra.smul_def]

end Semiring

section Ring

variable {R : Type u} [CommRing R]

/-- An ambient polynomial with equal endpoint evaluations is a constant plus a multiple of
`X² - X`. -/
@[stacks 00JG "conductor decomposition for equal-endpoint polynomials"]
theorem exists_eq_C_add_conductor_mul_of_eval_eq (f : R[X]) (hf : f.eval 0 = f.eval 1) :
    ∃ q : R[X], f = C (f.eval 0) + (X ^ 2 - X) * q := by
  have hunit : IsUnit ((0 : R) - 1) := by simp
  simpa [EvalEqualizer.vanishing, pow_two, mul_sub] using
    EvalEqualizer.exists_eq_C_add_vanishing_mul 0 1 hunit f hf

/-- An equal-endpoint polynomial is a constant plus a multiple of `X² - X`. -/
@[stacks 00JG "conductor decomposition in the equal-endpoint algebra"]
theorem exists_eq_C_add_conductor_mul (f : equalEndpoint R) :
    ∃ q : R[X], (f : R[X]) = C ((f : R[X]).eval 0) + (X ^ 2 - X) * q :=
  exists_eq_C_add_conductor_mul_of_eval_eq (f : R[X])
    ((mem_equalEndpoint (f : R[X])).mp f.property)

/-- The ambient polynomial algebra is finite over the equal-endpoint algebra. -/
@[stacks 00JG "finite equal-endpoint polynomial extension"]
noncomputable instance polynomialModuleFinite :
    Module.Finite (equalEndpoint R) R[X] :=
  EvalEqualizer.moduleFinite 0 1 (by simp)

section Noetherian

variable [IsNoetherianRing R]

/-- The equal-endpoint algebra is finite type over a Noetherian coefficient ring. -/
@[stacks 00JG "finite type equal-endpoint algebra"]
noncomputable instance finiteType :
    Algebra.FiniteType R (equalEndpoint R) :=
  Subalgebra.finiteType_of_finite (equalEndpoint R)

/-- The equal-endpoint algebra over a Noetherian coefficient ring is Noetherian. -/
@[stacks 00JG "Noetherian equal-endpoint algebra"]
noncomputable instance isNoetherianRing :
    IsNoetherianRing (equalEndpoint R) :=
  Algebra.FiniteType.isNoetherianRing R _

end Noetherian

end Ring

end EqualEndpoint

end Polynomial
