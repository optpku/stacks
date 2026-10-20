module

public import Mathlib.Algebra.Ring.Pi
public import Mathlib.Data.Finite.Defs
public import ReasLib.RingTheory.Topology.Adic.Complete
public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.WeakIdealCompletion.Properties

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

/-- A complete separated adic ring admitting a finitely generated ideal of definition. -/
class IsAdicStarRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsAdicRing R where
  /-- There is a finitely generated ideal of definition. -/
  exists_fg_isIdealOfDefinition :
    ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I

namespace IsAdicStarRing

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- An adic ring is adic-star if it admits a
finitely generated ideal of definition. -/
theorem of [IsAdicRing R]
    (h : ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I) :
    IsAdicStarRing R := sorry

/-- An adic-star ring is adic and has a finitely generated ideal of
definition. -/
theorem spec [IsAdicStarRing R] :
    IsAdicRing R ∧ ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I := sorry

/-- A topological ring is adic-star if and only if it is adic and has a
finitely generated ideal of definition. -/
theorem iff :
    IsAdicStarRing R ↔
      IsAdicRing R ∧ ∃ I : Ideal R, I.FG ∧ Ideal.IsIdealOfDefinition I := sorry

/-- A Noetherian adic ring is adic-star. -/
instance of_isNoetherianRing [IsAdicRing R] [IsNoetherianRing R] :
    IsAdicStarRing R := sorry

/-- An adic-star ring is countably indexed. -/
instance instIsCountablyIndexed [IsAdicStarRing R] : IsCountablyIndexed R :=
  sorry

/-- Finite products of adic-star rings are adic-star. -/
instance instPi {ι : Type u} [Finite ι] {A : ι → Type u}
    [∀ i, CommRing (A i)] [∀ i, TopologicalSpace (A i)]
    [∀ i, IsAdicStarRing (A i)] :
    IsAdicStarRing (∀ i, A i) := sorry

/-- The weak-ideal completion of an algebra over an adic-star ring is adic-star. -/
instance instWeakIdealCompletion {A A' : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
    [CommRing A'] [Algebra A A'] :
    IsAdicStarRing (weakIdealCompletion A A') := sorry

end IsAdicStarRing

end TopologicalRing
