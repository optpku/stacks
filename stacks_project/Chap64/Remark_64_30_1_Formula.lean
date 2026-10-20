/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Finsupp.Defs
public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.Divisors
public import stacks_project.Chap64.Remark_64_30_1_Coinvariants

/-!
# Abstract trace data and the abstract trace formula

This leaf owns the integer `q`, conjugacy-class multiplicities `S_d`, and the
laws `cd_ℓ(G) < ∞` and the displayed homology-side identity
`leftHandSum = (q^n) • Tr(F^n | LH_0(G, M))`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Action CategoryTheory.Action.ModuleCat
open scoped Ring

universe u v

namespace ProfiniteGrp

variable (S : DegreeExtension.{u})

/-- The numerical data of an abstract trace formula: an integer `q ≥ 1` and a
finitely supported multiplicity of degree-`d` conjugacy classes for each `d ≥ 1`. -/
structure AbstractTraceData where
  /-- The integer `q` appearing in the abstract trace formula. -/
  q : ℕ
  /-- The source constraint `q ≥ 1`. -/
  one_le_q : 1 ≤ q
  /-- Multiplicity of each conjugacy class in the degree-`d` set `S_d`. -/
  multiplicity : ℕ+ → (ConjClasses S.middle →₀ ℕ)
  /-- Classes with positive multiplicity have degree `d`. -/
  support_degree :
    ∀ (d : ℕ+) (c : ConjClasses S.middle),
      multiplicity d c ≠ 0 → S.degClass c = hatZNatCast d.val

namespace AbstractTraceData

variable {S : DegreeExtension.{u}}

/-- Recover abstract trace data from finite sets `S_d` and labels `F_x`. -/
noncomputable def ofFiniteSets (q : ℕ) (hq : 1 ≤ q)
    {ι : ℕ+ → Type u} [∀ d, Fintype (ι d)]
    (F : ∀ d, ι d → ConjClasses S.middle)
    (hdeg : ∀ d x, S.degClass (F d x) = hatZNatCast d.val) :
    AbstractTraceData S where
  q := q
  one_le_q := hq
  multiplicity := fun d => ∑ x : ι d, Finsupp.single (F d x) 1
  support_degree := sorry

/-- Scaling `q` by `m` and replacing each `S_d` by `m^d` copies, as numerical data.
This operation does not preserve the abstract trace identity. -/
noncomputable def scale (T : AbstractTraceData S) (m : ℕ) (hm : 1 ≤ m) :
    AbstractTraceData S where
  q := m * T.q
  one_le_q := Nat.mul_le_mul hm T.one_le_q
  multiplicity := fun d => m ^ d.val • T.multiplicity d
  support_degree := sorry

/-- The integer `q` of a scaled datum is `m * T.q`. -/
theorem scale_q (T : AbstractTraceData S) (m : ℕ) (hm : 1 ≤ m) :
    (T.scale m hm).q = m * T.q :=
  sorry

/-- Scaling multiplies the degree-`d` multiplicity by `m^d`. -/
theorem scale_multiplicity (T : AbstractTraceData S) (m : ℕ) (hm : 1 ≤ m) (d : ℕ+) :
    (T.scale m hm).multiplicity d = m ^ d.val • T.multiplicity d :=
  sorry

/-- The left-hand side of the abstract trace identity. -/
noncomputable def leftHandSum {Λ : Type v} [Ring Λ] (T : AbstractTraceData S)
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ) : Λ♮ :=
  ∑ d ∈ n.divisors,
    if h : 0 < d then
      d • (T.multiplicity ⟨d, h⟩).sum fun c m => m • conjClassTrace S M (powClass c (n / d))
    else
      0

/-- Weighted point count `∑_{d∣n} d ∑_c multiplicity d c`. -/
noncomputable def pointCount (T : AbstractTraceData S) (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors,
    if h : 0 < d then d * (T.multiplicity ⟨d, h⟩).sum fun _ m => m else 0

end AbstractTraceData

/-- The two laws of an abstract trace formula, relative to fixed numerical data.
The displayed identity is the homology form `leftHandSum = (q^n) • Tr(F^n | LH_0)`. -/
structure IsAbstractTraceFormula (T : AbstractTraceData S) : Prop where
  /-- For every `ℓ` not dividing `q`, the group `G = ker(deg)` has finite `ℓ`-cd. -/
  finite_cd :
    ∀ ℓ : ℕ, ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G
  /-- The displayed homology-side trace identity in `Λ♮`, for finite rings in which `q`
  is a unit. -/
  trace_eq :
    ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
      [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
      (hunit : IsUnit (T.q : Λ))
      (M : DiscreteModuleCat Λ S.middle)
      [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ),
      0 < n →
        T.leftHandSum M n =
          (T.q ^ n) •
            traceFrobeniusPow S M (isPerfect_derivedCoinvariants S M hunit finite_cd) n

/-- Constructor packaging the two abstract-trace-formula laws. -/
theorem IsAbstractTraceFormula.mk'
    (T : AbstractTraceData S)
    (hcd : ∀ ℓ : ℕ, ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G)
    (htr :
      ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
        [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
          (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
        (hunit : IsUnit (T.q : Λ))
        (M : DiscreteModuleCat Λ S.middle)
        [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ),
        0 < n →
          T.leftHandSum M n =
            (T.q ^ n) •
              traceFrobeniusPow S M (isPerfect_derivedCoinvariants S M hunit hcd) n) :
    IsAbstractTraceFormula S T where
  finite_cd := hcd
  trace_eq := htr

/-- The abstract trace formula unfolds as finite `ℓ`-cd together with the homology-side
trace identity. -/
theorem IsAbstractTraceFormula.spec (T : AbstractTraceData S) :
    IsAbstractTraceFormula S T ↔
      (∀ ℓ : ℕ, ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G) ∧
        ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
          [(Functor.Homotopy.toDerived (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
            (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G) (ComplexShape.up ℤ))]
          (hunit : IsUnit (T.q : Λ))
          (M : DiscreteModuleCat Λ S.middle)
          [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
          (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M)) (n : ℕ),
          0 < n → T.leftHandSum M n = (T.q ^ n) • traceFrobeniusPow S M hperf n :=
  sorry

/-- `Γ` has an abstract trace formula: there exist `q` and multiplicities `S_d`
satisfying the two laws. -/
def HasAbstractTraceFormula : Prop :=
  ∃ T : AbstractTraceData S, IsAbstractTraceFormula S T

/-- Existence of an abstract trace formula is equivalent to numerical data `T`
satisfying finite `ℓ`-cd and the homology-side identity. -/
theorem HasAbstractTraceFormula_iff :
    HasAbstractTraceFormula S ↔
      ∃ T : AbstractTraceData S,
        (∀ ℓ : ℕ, ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G) ∧
          ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
            [(Functor.Homotopy.toDerived
                (actionCoinvariantsFunctor Λ S.G)).HasLeftDerivedFunctor
              (HomotopyCategory.quasiIso (Action (ModuleCat.{u} Λ) S.G)
                (ComplexShape.up ℤ))]
            (hunit : IsUnit (T.q : Λ))
            (M : DiscreteModuleCat Λ S.middle)
            [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
            (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M)) (n : ℕ),
            0 < n →
              T.leftHandSum M n = (T.q ^ n) • traceFrobeniusPow S M hperf n :=
  sorry

/-- Given `q`, the multiplicities `S_d` are uniquely determined. -/
theorem AbstractTraceData.multiplicity_unique {T₁ T₂ : AbstractTraceData S}
    (h₁ : IsAbstractTraceFormula S T₁) (h₂ : IsAbstractTraceFormula S T₂)
    (hq : T₁.q = T₂.q) : T₁.multiplicity = T₂.multiplicity :=
  sorry

end ProfiniteGrp
