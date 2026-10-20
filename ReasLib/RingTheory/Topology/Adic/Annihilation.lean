/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Topology.Adic.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Annihilation of ideal powers by ideals of definition
-/

@[expose] public section

universe u

namespace TopologicalRing.Ideal

/-- An ideal `J` has a positive power annihilated by an ideal of definition
if there exist an ideal of definition `I` and a positive integer `n` with
`I * J ^ n = ⊥`. -/
def IsKilledByPowIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A]
    (J : Ideal A) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥

/-- An ideal has a positive power annihilated by an ideal of definition exactly
when there are an ideal of definition `I` and a positive integer `n` with
`I * J ^ n = ⊥`. -/
theorem isKilledByPowIdealOfDefinition_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) :
    IsKilledByPowIdealOfDefinition J ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥ :=
  Iff.rfl

namespace IsKilledByPowIdealOfDefinition

/-- If `I` is an ideal of definition and `I * J ^ n = ⊥` for some positive
integer `n`, then a positive power of `J` is annihilated by an ideal of definition. -/
theorem of_mul_pow {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (n : ℕ) (hn : 0 < n) (h : I * J ^ n = ⊥) :
    IsKilledByPowIdealOfDefinition J :=
  ⟨I, hI, n, hn, h⟩

/-- If `I` is an ideal of definition and `I * J = ⊥`, then a positive power of `J` is
annihilated by an ideal of definition. -/
theorem of_mul {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (h : I * J = ⊥) :
    IsKilledByPowIdealOfDefinition J := by
  exact of_mul_pow hI 1 Nat.zero_lt_one (by simpa only [pow_one] using h)

/-- If a positive power of `J` is annihilated by an ideal of definition, there
are an ideal of definition `I` and a positive integer `n` with `I * J ^ n = ⊥`. -/
theorem spec {A : Type u} [CommRing A] [TopologicalSpace A] {J : Ideal A}
    (h : IsKilledByPowIdealOfDefinition J) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ ∃ n : ℕ, 0 < n ∧ I * J ^ n = ⊥ :=
  h

end IsKilledByPowIdealOfDefinition

/-- An ideal `J` is killed by an ideal of definition if there exists an ideal
of definition `I` with `I * J = ⊥`. -/
def IsKilledByIdealOfDefinition {A : Type u} [CommRing A] [TopologicalSpace A]
    (J : Ideal A) : Prop :=
  ∃ I : Ideal A, IsIdealOfDefinition I ∧ I * J = ⊥

/-- An ideal is killed by an ideal of definition if and only if there exists an
ideal of definition `I` with `I * J = ⊥`. -/
theorem isKilledByIdealOfDefinition_iff {A : Type u} [CommRing A]
    [TopologicalSpace A] (J : Ideal A) :
    IsKilledByIdealOfDefinition J ↔
      ∃ I : Ideal A, IsIdealOfDefinition I ∧ I * J = ⊥ :=
  Iff.rfl

namespace IsKilledByIdealOfDefinition

/-- If `I` is an ideal of definition and `I * J = ⊥`, then `J` is killed by an
ideal of definition. -/
theorem of_mul {A : Type u} [CommRing A] [TopologicalSpace A] {J I : Ideal A}
    (hI : IsIdealOfDefinition I) (h : I * J = ⊥) :
    IsKilledByIdealOfDefinition J :=
  ⟨I, hI, h⟩

/-- If `J` is killed by an ideal of definition, there exists an ideal of
definition `I` with `I * J = ⊥`. -/
theorem spec {A : Type u} [CommRing A] [TopologicalSpace A] {J : Ideal A}
    (h : IsKilledByIdealOfDefinition J) :
    ∃ I : Ideal A, IsIdealOfDefinition I ∧ I * J = ⊥ :=
  h

/-- If an ideal is annihilated by an ideal of definition, then it has a positive
power annihilated by an ideal of definition. -/
theorem to_isKilledByPowIdealOfDefinition {A : Type u} [CommRing A]
    [TopologicalSpace A] {J : Ideal A} (h : IsKilledByIdealOfDefinition J) :
    IsKilledByPowIdealOfDefinition J := by
  obtain ⟨I, hI, hIJ⟩ := h
  exact IsKilledByPowIdealOfDefinition.of_mul hI hIJ

end IsKilledByIdealOfDefinition

end TopologicalRing.Ideal

