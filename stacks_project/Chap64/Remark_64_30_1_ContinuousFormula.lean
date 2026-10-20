module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.NumberTheory.Divisors
public import stacks_project.Chap64.Remark_64_30_1_ContinuousCoinvariants

/-!
# Full abstract continuous trace formula

Numerical data retain the original finite-family multiplicities. The predicate
quantifies over all finite rings and all finite projective left coefficients.
Perfectness is the well-definedness part of the source's derived trace clause,
not a consequence manufactured from finite prime cohomological dimension.
-/

@[expose] public section
open CategoryTheory CategoryTheory.Action.ModuleCat
open scoped Ring
noncomputable section
universe u v

namespace ProfiniteGrp.ContinuousTrace

variable (S : DegreeExtension.{u})

/-- The source integer and finite multiplicities of degree-d conjugacy classes. -/
structure AbstractTraceData where
  q : ℕ
  one_le_q : 1 ≤ q
  multiplicity : ℕ+ → (ConjClasses S.middle →₀ ℕ)
  support_degree : ∀ (d : ℕ+) (c : ConjClasses S.middle),
    multiplicity d c ≠ 0 → S.degClass c = hatZNatCast d.val

namespace AbstractTraceData
variable {S}

/-- Sum the actual finite family of Frobenius conjugacy classes, retaining multiplicity. -/
def ofFiniteSets (q : ℕ) (hq : 1 ≤ q)
    {ι : ℕ+ → Type u} [∀ d, Fintype (ι d)]
    (F : ∀ d, ι d → ConjClasses S.middle)
    (hdeg : ∀ d x, S.degClass (F d x) = hatZNatCast d.val) : AbstractTraceData S where
  q := q
  one_le_q := hq
  multiplicity d := ∑ x : ι d, Finsupp.single (F d x) 1
  support_degree := by
    intro d c hc
    by_contra h
    apply hc
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro x hx
    exact Finsupp.single_eq_of_ne (fun he ↦ h (he.symm ▸ hdeg d x))

/-- The source's full divisor sum in the additive commutator quotient. -/
def leftHandSum {Λ : Type v} [Ring Λ] (T : AbstractTraceData S)
    (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ) : Λ♮ :=
  ∑ d ∈ n.divisors, if h : 0 < d then
    d • (T.multiplicity ⟨d, h⟩).sum (fun c m ↦ m • conjClassTrace S M (powClass S c (n / d)))
  else 0

/-- The integer weighted count of all source degree-d classes. -/
def pointCount (T : AbstractTraceData S) (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, if h : 0 < d then
    d * (T.multiplicity ⟨d, h⟩).sum (fun _ m ↦ m)
  else 0

@[simp] theorem ofFiniteSets_q (q : ℕ) (hq : 1 ≤ q)
    {ι : ℕ+ → Type u} [∀ d, Fintype (ι d)]
    (F : ∀ d, ι d → ConjClasses S.middle)
    (hdeg : ∀ d x, S.degClass (F d x) = hatZNatCast d.val) :
    (ofFiniteSets q hq F hdeg).q = q := rfl

end AbstractTraceData

/-- The full source formula, including well-definedness of every derived trace.
All three fields are propositions. No perfect model or isomorphism is selected here. -/
structure IsAbstractTraceFormula (T : AbstractTraceData S) : Prop where
  finite_cd : ∀ ℓ : ℕ, Nat.Prime ℓ → ¬ ℓ ∣ T.q → HasFiniteEllCohomologicalDimension ℓ S.G
  homology_perfect : ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
    (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V],
    DerivedCategory.IsPerfect (derivedCoinvariants S M)
  trace_eq : ∀ {Λ : Type u} [Ring Λ] [Finite Λ]
    (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V] (n : ℕ),
    0 < n → T.leftHandSum M n =
      (T.q ^ n) • traceFrobeniusPow S M (homology_perfect hunit M) n

/-- The trace law is unchanged by choosing a different proof of perfectness;
this only varies a proof, never the underlying continuous homology model. -/
theorem IsAbstractTraceFormula.trace_eq_of_perfect {T : AbstractTraceData S}
    (h : IsAbstractTraceFormula S T) {Λ : Type u} [Ring Λ] [Finite Λ]
    (hunit : IsUnit (T.q : Λ)) (M : DiscreteModuleCat Λ S.middle)
    [Module.Finite Λ M.obj.V] [Module.Projective Λ M.obj.V]
    (hperf : DerivedCategory.IsPerfect (derivedCoinvariants S M)) (n : ℕ) (hn : 0 < n) :
    T.leftHandSum M n = (T.q ^ n) • traceFrobeniusPow S M hperf n :=
  h.trace_eq hunit M n hn

/-- Source existence quantifies numerical data, without adding derived-model inputs. -/
def HasAbstractTraceFormula : Prop :=
  ∃ T : AbstractTraceData S, IsAbstractTraceFormula S T

end ProfiniteGrp.ContinuousTrace
