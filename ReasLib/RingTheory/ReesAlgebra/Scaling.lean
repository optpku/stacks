/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.ReesAlgebra.Grading

/-!
# Principal Scaling of Rees Algebras

This leaf packages the functorial map obtained by replacing the Rees variable
`t` with `f * t`.  It is independent of any homogeneous localization or
affine blowup chart.

@stack 0BBI
-/

@[expose] public section

noncomputable section

universe u

open Polynomial

namespace ReesAlgebra.Scaling

section

variable {R : Type u} [CommRing R]

/-- The principal scaling `fI = (f) * I` of an ideal `I`. -/
@[stacks 0BBI "principal scaling of an ideal"]
def ideal (I : Ideal R) (f : R) : Ideal R :=
  Ideal.span ({f} : Set R) * I

/-- The product `f * a` belongs to the principal scaling `Scaling.ideal I f`. -/
@[stacks 0BBI "membership in a principal ideal scaling"]
theorem element_mem (I : Ideal R) (a : I) (f : R) :
    f * a ∈ ideal I f := sorry

/-- The distinguished element `f * a` of the scaled ideal `Scaling.ideal I f`. -/
@[stacks 0BBI "principal scaling of an ideal element"]
def element (I : Ideal R) (a : I) (f : R) : ideal I f :=
  ⟨f * a, element_mem I a f⟩

/-- Membership in a power of `Scaling.ideal I f` is equivalent to divisibility by `f ^ n`
with quotient in `I ^ n`. -/
@[stacks 0BBI "power membership for a principal ideal scaling"]
theorem mem_ideal_pow_iff (I : Ideal R) (f : R) (n : ℕ) (x : R) :
    x ∈ ideal I f ^ n ↔ ∃ y : ↥(I ^ n), f ^ n * y = x := sorry

/-- The codomain predicate needed to construct the principal scaling ring homomorphism. -/
theorem ringHom_mem (I : Ideal R) (f : R) (x : (reesAlgebra I).toSubring) :
    ((Polynomial.eval₂RingHom C (C f * X)).comp (reesAlgebra I).toSubring.subtype) x ∈
      (reesAlgebra (ideal I f)).toSubring := sorry

/-- The Rees-algebra map induced by substituting `t ↦ f * t`. -/
@[stacks 0BBI "principal scaling map of Rees algebras"]
noncomputable def ringHom (I : Ideal R) (f : R) :
    reesAlgebra I →+* reesAlgebra (ideal I f) :=
  RingHom.codRestrict
    ((Polynomial.eval₂RingHom C (C f * X)).comp (reesAlgebra I).toSubring.subtype)
    (reesAlgebra (ideal I f)).toSubring
    (ringHom_mem I f)

/-- The polynomial underlying `Scaling.ringHom I f x` is obtained by substituting `f * X`. -/
@[stacks 0BBI "principal scaling map evaluation", simp]
theorem ringHom_apply (I : Ideal R) (f : R) (x : reesAlgebra I) :
    ((ringHom I f x : reesAlgebra (ideal I f)) : R[X]) =
      Polynomial.eval₂ C (C f * X) (x : R[X]) := sorry

/-- `Scaling.ringHom I f` multiplies the coefficient of a degree-`n` monomial by `f ^ n`. -/
@[stacks 0BBI "principal scaling of a Rees monomial"]
theorem ringHom_monomial (I : Ideal R) (f : R) (n : ℕ) (y : ↥(I ^ n)) :
    ringHom I f
        (⟨Polynomial.monomial n y, (reesAlgebra.monomial_mem).2 y.2⟩ : reesAlgebra I) =
      ⟨Polynomial.monomial n (f ^ n * y),
        (reesAlgebra.monomial_mem).2 ((mem_ideal_pow_iff I f n _).2 ⟨y, rfl⟩)⟩ := sorry

/-- Principal scaling preserves every homogeneous Rees component. -/
@[stacks 0BBI "principal scaling preserves Rees degree"]
theorem ringHom_mem_grade (I : Ideal R) (f : R) {n : ℕ} {x : reesAlgebra I}
    (hx : x ∈ ReesAlgebra.Grading.grade I n) :
    ringHom I f x ∈ ReesAlgebra.Grading.grade (ideal I f) n := sorry

/-- The graded Rees-algebra map induced by principal scaling. -/
@[stacks 0BBI "principal scaling map of graded Rees algebras"]
noncomputable def gradedHom (I : Ideal R) (f : R) :
    ReesAlgebra.Grading.grade I →+*ᵍ ReesAlgebra.Grading.grade (ideal I f) where
  toRingHom := ringHom I f
  map_mem := ringHom_mem_grade I f

/-- Principal scaling sends the degree-one element `a t` to `(f a) t`. -/
@[stacks 0BBI "principal scaling of a degree-one Rees element"]
theorem gradedHom_degreeOne (I : Ideal R) (a : I) (f : R) :
    gradedHom I f (ReesAlgebra.Grading.degreeOne I a) =
      ReesAlgebra.Grading.degreeOne (ideal I f) (element I a f) := sorry

/-- Principal scaling is the identity on the degree-zero scalar copy of `R`. -/
@[stacks 0BBI "principal scaling on degree-zero Rees scalars"]
theorem gradedHom_zeroAlgebraMap (I : Ideal R) (f r : R) :
    (gradedHom I f).gradedAddHom 0 (ReesAlgebra.Grading.zeroAlgebraMap I r) =
      ReesAlgebra.Grading.zeroAlgebraMap (ideal I f) r := sorry

end

end ReesAlgebra.Scaling
