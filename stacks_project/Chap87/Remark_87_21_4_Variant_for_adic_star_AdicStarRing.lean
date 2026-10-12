/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap87.Lemma_87_21_1

/-!
# Adic rings with a finitely generated ideal of definition

Objects of `WAdm^{adic*}` are complete separated adic rings that admit a
finitely generated ideal of definition. Finite products, countable indexing,
and weak-ideal completions stay in this class, so locality squares for
morphisms of `WAdm^{adic*}` can reuse `LocalizeSquare`.
-/

@[expose] public section

universe u

namespace TopologicalRing

/-- An object of `WAdm^{adic*}`: an adic ring with a finitely generated ideal
of definition. -/
class IsAdicStarRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsAdicRing R where
  /-- There is a finitely generated ideal of definition. -/
  exists_fg_isIdealOfDefinition :
    ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I

namespace IsAdicStarRing

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- Exhibit an object of `WAdm^{adic*}` by an adic ring together with a
finitely generated ideal of definition. -/
theorem of [IsAdicRing R]
    (h : ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I) :
    IsAdicStarRing R := sorry

/-- An object of `WAdm^{adic*}` is adic and has a finitely generated ideal of
definition. -/
theorem spec [IsAdicStarRing R] :
    IsAdicRing R ∧ ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I := sorry

/-- A topological ring is an object of `WAdm^{adic*}` iff it is adic and has a
finitely generated ideal of definition. -/
theorem iff :
    IsAdicStarRing R ↔
      IsAdicRing R ∧ ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I := sorry

/-- A Noetherian adic ring is an object of `WAdm^{adic*}`. -/
instance of_isNoetherianRing [IsAdicRing R] [IsNoetherianRing R] :
    IsAdicStarRing R := sorry

/-- An object of `WAdm^{adic*}` is countably indexed. -/
instance instIsCountablyIndexed [IsAdicStarRing R] : IsCountablyIndexed R :=
  sorry

/-- Finite products of objects of `WAdm^{adic*}` remain in `WAdm^{adic*}`. -/
instance instPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsAdicStarRing (A i)] :
    IsAdicStarRing (∀ i, A i) := sorry

/-- Weak-ideal completion of an algebra over an object of `WAdm^{adic*}`
remains in `WAdm^{adic*}`. -/
instance instWeakIdealCompletion {A A' : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing A'] [Algebra A A'] :
    IsAdicStarRing (weakIdealCompletion A A') := sorry

end IsAdicStarRing

end TopologicalRing
