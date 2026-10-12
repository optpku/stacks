/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Composition factors of modules

This file owns the concrete quotient module attached to a step of a composition
series.  Ring-theoretic invariants of that quotient are grouped in the
`Module.CompositionSeries.Factor` namespace, leaving the root
`CompositionSeries.factor` available for composition series in general
abelian categories.
-/

@[expose] public section

universe u v

namespace Module.CompositionSeries

section Ring

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The `i`-th composition factor is the quotient of the next submodule by its predecessor. -/
@[stacks 00J3 "composition factor"]
abbrev factor (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :=
  (s i.succ) ⧸ (s i.castSucc).comap (s i.succ).subtype

/-- The composition factor agrees with the quotient presentation using `Submodule.submoduleOf`. -/
theorem factor_eq_quotient_submoduleOf
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    factor s i = ((s i.succ) ⧸ (s i.castSucc).submoduleOf (s i.succ)) := sorry

namespace Factor

/-- Every factor of a composition series is simple. -/
@[stacks 00J3 "(2)"]
theorem isSimple (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    IsSimpleModule R (factor s i) := sorry

/- `factor` is deliberately an `abbrev`, matching Mathlib's quotient views. A global
`IsSimpleModule` instance would therefore have an overbroad reducible head and could match
unrelated quotient modules during typeclass search; consumers should use `Factor.isSimple`. -/

end Factor

end Ring

section CommRing

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

namespace Factor

/-- The annihilator of a composition factor is maximal. -/
@[stacks 00J3 "(3), maximal annihilator"]
theorem annihilatorIsMaximal
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (Module.annihilator R (factor s i)).IsMaximal := sorry

/-- The maximal-spectrum point canonically attached to a composition factor. -/
@[stacks 00J3 "(3), annihilator point"]
def annihilatorPoint
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) : MaximalSpectrum R :=
  ⟨Module.annihilator R (factor s i), annihilatorIsMaximal s i⟩

/-- The ideal underlying the annihilator point is the annihilator of the factor. -/
@[simp]
theorem annihilatorPoint_asIdeal
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    (annihilatorPoint s i).asIdeal = Module.annihilator R (factor s i) := sorry

/-- Equality of annihilator points is detected on their underlying annihilator ideals. -/
@[simp]
theorem annihilatorPoint_eq_iff
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) (m : MaximalSpectrum R) :
    annihilatorPoint s i = m ↔ Module.annihilator R (factor s i) = m.asIdeal := sorry

/-- A composition factor is linearly equivalent to the quotient by its annihilator. -/
@[stacks 00J3 "(3), quotient by annihilator"]
theorem nonemptyLinearEquivQuotientAnnihilator
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    Nonempty (factor s i ≃ₗ[R] R ⧸ Module.annihilator R (factor s i)) := sorry

/-- A composition factor is linearly equivalent to the quotient by its canonical annihilator
point. -/
theorem nonemptyLinearEquivQuotient
    (s : CompositionSeries (Submodule R M)) (i : Fin s.length) :
    Nonempty (factor s i ≃ₗ[R] R ⧸ (annihilatorPoint s i).asIdeal) := sorry

end Factor

/-- The multiplicity of a maximal ideal in a composition series is the number of factors having
that annihilator point. -/
@[stacks 00J3 "composition-factor multiplicity"]
noncomputable def multiplicity
    (s : CompositionSeries (Submodule R M)) (m : MaximalSpectrum R) : ℕ :=
  Set.ncard {i : Fin s.length |
    Module.annihilator R (factor s i) = m.asIdeal}

/-- A maximal ideal has positive multiplicity exactly when it occurs as an annihilator point. -/
@[simp]
theorem multiplicity_pos_iff
    (s : CompositionSeries (Submodule R M)) (m : MaximalSpectrum R) :
    0 < multiplicity s m ↔ ∃ i : Fin s.length, Factor.annihilatorPoint s i = m := sorry

/-- A weighted sum over the factors regroups by annihilator-point multiplicity. This purely
combinatorial form works in every additive commutative monoid and requires no endpoints for the
composition series or enumeration of the maximal spectrum. -/
@[stacks 00J3 "weighted composition-factor multiplicity finsum"]
theorem sum_factorWeight_eq_finsum_multiplicity_nsmul
    {N : Type*} [AddCommMonoid N]
    (s : CompositionSeries (Submodule R M)) (w : MaximalSpectrum R → N) :
    ∑ i : Fin s.length, w (Factor.annihilatorPoint s i) =
      ∑ᶠ m : MaximalSpectrum R, multiplicity s m • w m := sorry

end CommRing

section JordanHolder

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Jordan-Hölder for modules: two composition series with the same endpoints have linearly
equivalent factors after reindexing. -/
@[stacks 0FCK "module composition-series factors"]
theorem jordanHolderFactors
    (F G : CompositionSeries (Submodule R M))
    (hF₀ : F.head = ⊥) (hF₁ : F.last = ⊤)
    (hG₀ : G.head = ⊥) (hG₁ : G.last = ⊤) :
    ∃ σ : Fin F.length ≃ Fin G.length,
      ∀ i : Fin F.length, Nonempty (factor F i ≃ₗ[R] factor G (σ i)) := sorry

end JordanHolder

end Module.CompositionSeries
