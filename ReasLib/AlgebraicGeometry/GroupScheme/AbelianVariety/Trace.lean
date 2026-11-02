/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Trace
public import ReasLib.Algebra.Group.Torsion.Map
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety
public import ReasLib.AlgebraicGeometry.GroupScheme.AbelianVariety.Dimension
public import ReasLib.AlgebraicGeometry.GroupScheme.RationalPoints
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree

@[expose] public section

open AlgebraicGeometry CategoryTheory MonoidalCategory
open scoped AlgebraicGeometry CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.AbelianVariety

variable {k : Type u} [Field k]
variable {A : SchemeOverField k} [GrpObj A] [AbelianVariety A]

/-- Postcomposition with a group-scheme endomorphism of an abelian variety. -/
def homCompRight (f : A ⟶ A) [IsMonHom f] :
    (𝟙_ (SchemeOverField k) ⟶ A) →* (𝟙_ (SchemeOverField k) ⟶ A) where
  toFun p := p ≫ f
  map_one' := MonObj.one_comp f
  map_mul' p q := MonObj.mul_comp p q f

/-- The additive endomorphism induced on the group of rational points. -/
def rationalPointsMap (f : A ⟶ A) [IsMonHom f] :
    SchemeOverField.rationalPoints A →+ SchemeOverField.rationalPoints A :=
  (homCompRight f).toAdditive

/-- Rational `ℓ`-torsion of an abelian variety is a `ZMod ℓ`-module. -/
instance instModule_rationalTorsion (ℓ : ℕ) [NeZero ℓ] :
    Module (ZMod ℓ)
      (AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) (ℓ : ℤ)) :=
  AddSubgroup.torsionBy.zmodModule

/-- The linear action induced on rational `ℓ`-torsion by an abelian-variety endomorphism.
Here `ℓ` can be composite: the carrier is the subgroup killed by the integer `ℓ`, and
`toZModLinearMap` uses the scalar action induced by integer multiplication. -/
def rationalTorsionMap (f : A ⟶ A) [IsMonHom f] (ℓ : ℕ) [NeZero ℓ] :
    Module.End (ZMod ℓ)
      (AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) (ℓ : ℤ)) :=
  AddMonoidHom.toZModLinearMap ℓ
    ((rationalPointsMap f).torsionByMap (ℓ : ℤ))

/-- On rational points, the torsion action is induced by postcomposition. -/
theorem rationalTorsionMap_apply (f : A ⟶ A) [IsMonHom f] (ℓ : ℕ) [NeZero ℓ]
    (p : AddSubgroup.torsionBy (SchemeOverField.rationalPoints A) (ℓ : ℤ)) :
    (rationalTorsionMap f ℓ p).val = rationalPointsMap f p.val := rfl

/-- The function-field degree of an abelian-variety endomorphism, extended by zero
to non-dominant maps. For group endomorphisms, the dominant maps are precisely the
isogenies. The algebra structure is the one induced by `f`, not the identity algebra
structure on the underlying function field. -/
def endomorphismDegree (f : A ⟶ A) : ℕ :=
  open Classical in
  if h : IsDominant f.left then
    letI := h
    f.left.inducedFunctionFieldDegree
  else 0

/-- On dominant maps, the degree is the degree of the induced function-field extension. -/
theorem endomorphismDegree_of_isDominant (f : A ⟶ A) [h : IsDominant f.left] :
    endomorphismDegree f = f.left.inducedFunctionFieldDegree := by
  simp only [endomorphismDegree, dif_pos h]

/-- Non-dominant endomorphisms have degree zero. -/
theorem endomorphismDegree_of_not_isDominant (f : A ⟶ A) (h : ¬ IsDominant f.left) :
    endomorphismDegree f = 0 := by
  simp [endomorphismDegree, h]

/-- The integer trace, constructed by finite differences of function-field degrees.

For `d = 2 * dimension A > 0`, the classical degree polynomial
`P_f(T) = deg([T] - f)` is monic of degree `d`; its next coefficient is minus the
Tate-module trace. Consequently
`Δ^(d-1) P_f(0) = (d-1)! * (d.choose 2 - Tr(f))`.
The formula below extracts this coefficient using integer arithmetic. In the
multiplicative notation for group-object morphisms, `(𝟙 A) ^ i / f` is `[i] - f`.
For dimension zero the trace is zero.

This is the integer `Tr_J` used in Stacks, tag `03U1` (`trace.tex`, Weil's theorem).
The compatibility in tag `03U3`, proof, identifies its reduction modulo prime powers
with the trace on torsion. Existence and integrality of the degree polynomial and
compatibility with torsion remain proof obligations of the theorems below; no
witness is extracted from those obligations to define this integer. -/
def endomorphismTrace (f : A ⟶ A) [IsMonHom f] : ℤ :=
  let d := 2 * dimension A
  if d = 0 then 0 else
    (d.choose 2 : ℤ) -
      (∑ i ∈ Finset.range d, (-1 : ℤ) ^ (d - 1 - i) * ((d - 1).choose i : ℤ) *
        (endomorphismDegree ((𝟙 A) ^ i / f) : ℤ)) / ((d - 1).factorial : ℤ)

/-- The finite-difference construction extracts minus the next-to-leading coefficient
of any monic degree polynomial for `f`. This comparison does not choose a polynomial. -/
theorem endomorphismTrace_eq_neg_coeff (f : A ⟶ A) [IsMonHom f]
    (hA : 0 < dimension A) (P : Polynomial ℤ) (hmonic : P.Monic)
    (hdegree : P.natDegree = 2 * dimension A)
    (heval : ∀ n : ℕ, P.eval (n : ℤ) =
      (endomorphismDegree ((𝟙 A) ^ n / f) : ℤ)) :
    endomorphismTrace f = -P.coeff (2 * dimension A - 1) := sorry

/-- A zero-dimensional abelian variety has integer trace zero. -/
theorem endomorphismTrace_of_dimension_eq_zero (f : A ⟶ A) [IsMonHom f]
    (hA : dimension A = 0) : endomorphismTrace f = 0 := by
  simp [endomorphismTrace, hA]

/-- The integer trace reduces modulo every nonzero unit `ℓ` in the field.
Over an algebraically closed field this torsion group is free of rank
`2 * dimension A` over `ZMod ℓ`, also for composite `ℓ`; the prime-power trace
compatibilities combine by the Chinese remainder theorem. -/
theorem endomorphismTrace_spec (f : A ⟶ A) [IsMonHom f] [IsAlgClosed k]
    (ℓ : ℕ) [NeZero ℓ] (hℓ : IsUnit (ℓ : k)) :
    LinearMap.trace (ZMod ℓ) _ (rationalTorsionMap f ℓ) =
      (endomorphismTrace f : ZMod ℓ) := sorry

/-- An integer with all modular torsion traces equals the integer trace. -/
theorem endomorphismTrace_unique (f : A ⟶ A) [IsMonHom f] [IsAlgClosed k] (t : ℤ)
    (ht : ∀ (ℓ : ℕ) [NeZero ℓ], IsUnit (ℓ : k) →
      LinearMap.trace (ZMod ℓ) _ (rationalTorsionMap f ℓ) = (t : ZMod ℓ)) :
    t = endomorphismTrace f := sorry

end AlgebraicGeometry.AbelianVariety
