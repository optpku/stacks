module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.LinearAlgebra.QuadraticForm.Radical
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.MvPowerSeries.Order

@[expose] public section

noncomputable section

universe u

open MvPowerSeries QuadraticMap

/-- The homogeneous quadratic series `a * X 0 ^ 2 + b * X 0 * X 1 + c * X 1 ^ 2`. -/
def MvPowerSeries.quadraticSeries {k : Type u} [CommRing k] (a b c : k) :
    MvPowerSeries (Fin 2) k :=
  C a * X (0 : Fin 2) ^ 2 + C b * (X (0 : Fin 2) * X (1 : Fin 2)) + C c * X (1 : Fin 2) ^ 2

/-- Unfold `MvPowerSeries.quadraticSeries`. -/
theorem MvPowerSeries.quadraticSeries_def {k : Type u} [CommRing k] (a b c : k) :
    quadraticSeries a b c =
      C a * X (0 : Fin 2) ^ 2 + C b * (X (0 : Fin 2) * X (1 : Fin 2)) +
        C c * X (1 : Fin 2) ^ 2 := sorry

/-- The binary quadratic form `a * x ^ 2 + b * x * y + c * y ^ 2` on `Fin 2 → k`. -/
def binaryQuadratic {k : Type u} [CommRing k] (a b c : k) : QuadraticForm k (Fin 2 → k) :=
  a • proj (0 : Fin 2) 0 + b • proj (0 : Fin 2) 1 + c • proj (1 : Fin 2) 1

/-- Evaluation of `binaryQuadratic a b c`. -/
theorem binaryQuadratic_apply {k : Type u} [CommRing k] (a b c : k) (v : Fin 2 → k) :
    binaryQuadratic a b c v = a * v 0 ^ 2 + b * (v 0 * v 1) + c * v 1 ^ 2 := sorry

/-- In characteristic two, the binary quadratic form is nondegenerate exactly when its mixed
coefficient is nonzero. -/
theorem binaryQuadratic_nondegenerate_iff_of_charTwo {k : Type u} [Field k] [CharP k 2]
    (a b c : k) :
    (binaryQuadratic a b c).Nondegenerate ↔ b ≠ 0 := sorry

/-- A power series has initial term of degree two equal to a nondegenerate binary quadratic. -/
def MvPowerSeries.hasNondegenerateQuadraticInitial {k : Type u} [Field k]
    (f : MvPowerSeries (Fin 2) k) (a b c : k) : Prop :=
  f.order = 2 ∧ homogeneousComponent 2 f = quadraticSeries a b c ∧
    (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ (binaryQuadratic a b c).Nondegenerate

/-- Unfold `MvPowerSeries.hasNondegenerateQuadraticInitial`. -/
theorem MvPowerSeries.hasNondegenerateQuadraticInitial_iff {k : Type u} [Field k]
    (f : MvPowerSeries (Fin 2) k) (a b c : k) :
    hasNondegenerateQuadraticInitial f a b c ↔
      f.order = 2 ∧ homogeneousComponent 2 f = quadraticSeries a b c ∧
        (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ (binaryQuadratic a b c).Nondegenerate := sorry

/-- A nondegenerate binary quadratic, viewed as a series, has itself as initial term. -/
theorem MvPowerSeries.hasNondegenerateQuadraticInitial_quadraticSeries {k : Type u} [Field k]
    (a b c : k) (hq : 4 * a * c - b ^ 2 ≠ 0) :
    hasNondegenerateQuadraticInitial (quadraticSeries a b c) a b c := sorry

/-- A ring is presented by a finite separable power-series quotient with nondegenerate quadratic
initial term. -/
def IsOrdinaryDoublePointRing (k : Type u) (A : Type u)
    [Field k] [CommRing A] [Algebra k A] : Prop :=
  ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (f : MvPowerSeries (Fin 2) k')
    (a b c : k'),
    FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧
      hasNondegenerateQuadraticInitial f a b c ∧
        Nonempty ((MvPowerSeries (Fin 2) k' ⧸ Ideal.span {f}) ≃ₐ[k] A)

/-- The defining finite-separable coefficient extension, quadratic initial term, and quotient
presentation of an ordinary double point ring. -/
theorem isOrdinaryDoublePointRing_iff (k : Type u) (A : Type u)
    [Field k] [CommRing A] [Algebra k A] :
    IsOrdinaryDoublePointRing k A ↔
      ∃ (k' : Type u) (_ : Field k') (_ : Algebra k k') (f : MvPowerSeries (Fin 2) k')
        (a b c : k'),
        FiniteDimensional k k' ∧ Algebra.IsSeparable k k' ∧ f.order = 2 ∧
          homogeneousComponent 2 f = quadraticSeries a b c ∧
          (a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0) ∧ (binaryQuadratic a b c).Nondegenerate ∧
          Nonempty ((MvPowerSeries (Fin 2) k' ⧸ Ideal.span {f}) ≃ₐ[k] A) := sorry

/-- Every nondegenerate binary quadratic over a finite separable extension presents an ordinary
double point ring. -/
theorem isOrdinaryDoublePointRing_quadraticSeries (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k'] (a b c : k')
    (hq : 4 * a * c - b ^ 2 ≠ 0) :
    IsOrdinaryDoublePointRing k
      (MvPowerSeries (Fin 2) k' ⧸ Ideal.span {quadraticSeries a b c}) := sorry

/-- Two pairs `(k', q)` of finite separable coefficient fields and binary quadratics over `k`
are equivalent when a `k`-algebra equivalence of coefficient fields carries one form to a unit
multiple of a form equivalent to the other. -/
def binaryQuadratic.EquivalentPair (k k₁ k₂ : Type u)
    [Field k] [Field k₁] [Field k₂] [Algebra k k₁] [Algebra k k₂]
    (a₁ b₁ c₁ : k₁) (a₂ b₂ c₂ : k₂) : Prop :=
  ∃ (e : k₁ ≃ₐ[k] k₂) (u : k₂ˣ),
    Equivalent (binaryQuadratic (e a₁) (e b₁) (e c₁))
      ((u : k₂) • binaryQuadratic a₂ b₂ c₂)

/-- Unfold `binaryQuadratic.EquivalentPair`. -/
theorem binaryQuadratic.equivalentPair_iff (k k₁ k₂ : Type u)
    [Field k] [Field k₁] [Field k₂] [Algebra k k₁] [Algebra k k₂]
    (a₁ b₁ c₁ : k₁) (a₂ b₂ c₂ : k₂) :
    binaryQuadratic.EquivalentPair k k₁ k₂ a₁ b₁ c₁ a₂ b₂ c₂ ↔
      ∃ (e : k₁ ≃ₐ[k] k₂) (u : k₂ˣ),
        Equivalent (binaryQuadratic (e a₁) (e b₁) (e c₁))
          ((u : k₂) • binaryQuadratic a₂ b₂ c₂) := sorry

/-- Presented ordinary double point rings are equivalent exactly when their coefficient-field and
binary-quadratic pairs are equivalent. -/
theorem ordinaryDoublePointRing_iso_iff_quadraticPair (k k₁ k₂ : Type u)
    [Field k] [Field k₁] [Field k₂] [Algebra k k₁] [Algebra k k₂]
    [FiniteDimensional k k₁] [Algebra.IsSeparable k k₁]
    [FiniteDimensional k k₂] [Algebra.IsSeparable k k₂]
    (f₁ : MvPowerSeries (Fin 2) k₁) (a₁ b₁ c₁ : k₁)
    (hf₁ : hasNondegenerateQuadraticInitial f₁ a₁ b₁ c₁)
    (f₂ : MvPowerSeries (Fin 2) k₂) (a₂ b₂ c₂ : k₂)
    (hf₂ : hasNondegenerateQuadraticInitial f₂ a₂ b₂ c₂) :
    Nonempty
        ((MvPowerSeries (Fin 2) k₁ ⧸ Ideal.span {f₁}) ≃ₐ[k]
          (MvPowerSeries (Fin 2) k₂ ⧸ Ideal.span {f₂})) ↔
      binaryQuadratic.EquivalentPair k k₁ k₂ a₁ b₁ c₁ a₂ b₂ c₂ := sorry

