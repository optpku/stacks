/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import ReasLib.CategoryTheory.Filtration.Exhaustive

@[expose] public section

universe v u

namespace CategoryTheory.CohomologicalSpectralSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {initialPage : ℤ}

/-- A cohomological spectral sequence finitely abuts to `H` if each total-degree target has
a finite decreasing filtration whose graded pieces identify with all sufficiently late pages,
and all incoming and outgoing differentials at each bidegree eventually vanish. -/
def FinitelyAbutsTo (E : CohomologicalSpectralSequence C initialPage) (H : ℤ → C) : Prop :=
  ∃ filtration : ∀ degree : ℤ, DecreasingFiltration (H degree),
    (∀ degree : ℤ, IndexedFiltration.IsFinite (filtration degree)) ∧
      ∀ p q : ℤ, ∃ bound : ℤ, ∀ (r : ℤ) (hr : initialPage ≤ r), bound ≤ r →
        (∀ other : ℤ × ℤ,
          (E.page r hr).d (p, q) other = 0 ∧ (E.page r hr).d other (p, q) = 0) ∧
        Nonempty ((E.page r hr).X (p, q) ≅
          Limits.cokernel ((filtration (p + q)).succInclusion p))

end CategoryTheory.CohomologicalSpectralSequence

namespace CategoryTheory.CohomologicalSpectralSequenceNat

variable {C : Type u} [Category.{v} C] [Abelian C] {initialPage : ℤ}

/-- A first-quadrant cohomological spectral sequence finitely abuts to `H` if each `H n`
has a decreasing filtration with stage `0` equal to the whole object and stage `n + 1`
equal to zero, all incoming and outgoing differentials eventually vanish at each bidegree,
and all sufficiently late page entries identify with the corresponding graded pieces. -/
def FinitelyAbutsTo (E : CohomologicalSpectralSequenceNat C initialPage) (H : ℕ → C) : Prop :=
  ∃ filtration : ∀ degree : ℕ, DecreasingFiltration (H degree),
    (∀ degree : ℕ, filtration degree 0 = ⊤ ∧
      filtration degree (Int.ofNat (degree + 1)) = ⊥) ∧
      ∀ p q : ℕ, ∃ bound : ℤ, ∀ (r : ℤ) (hr : initialPage ≤ r), bound ≤ r →
        (∀ other : ℕ × ℕ,
          (E.page r hr).d (p, q) other = 0 ∧ (E.page r hr).d other (p, q) = 0) ∧
        Nonempty ((E.page r hr).X (p, q) ≅
          Limits.cokernel ((filtration (p + q)).succInclusion (Int.ofNat p)))

end CategoryTheory.CohomologicalSpectralSequenceNat
