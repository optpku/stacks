module

public import ReasLib.RingTheory.Topology.WeakIdealCompletion
public import ReasLib.RingTheory.Topology.CountablyIndexed
public import ReasLib.RingTheory.Topology.Adic.Weakly
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Preservation properties of weak-ideal completion
-/

@[expose] public section

universe u

namespace TopologicalRing.weakIdealCompletion

variable {A A' : Type u}
variable [CommRing A] [TopologicalSpace A] [CommRing A'] [Algebra A A']

/-- The weak-ideal completion of an algebra over a countably indexed weakly admissible
ring is countably indexed. -/
instance instIsCountablyIndexed [IsWeaklyAdmissibleRing A] [IsCountablyIndexed A] :
    IsCountablyIndexed (weakIdealCompletion A A') := sorry

/-- The weak-ideal completion of an algebra over an admissible ring is admissible. -/
instance instIsAdmissibleRing [IsAdmissibleRing A] :
    IsAdmissibleRing (weakIdealCompletion A A') := sorry

/-- The weak-ideal completion of an algebra over a weakly adic ring is weakly adic. -/
instance instIsWeaklyAdicRing [IsWeaklyAdicRing A] :
    IsWeaklyAdicRing (weakIdealCompletion A A') := sorry

/-- The weak-ideal completion of an algebra over an adic ring with a finitely generated
ideal of definition is adic. -/
theorem isAdicRing [IsAdicRing A]
    (hA : ∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I) :
    IsAdicRing (weakIdealCompletion A A') := sorry

/-- The weak-ideal completion of an algebra over an adic ring with a finitely generated
ideal of definition has a finitely generated ideal of definition. -/
theorem exists_fg_isIdealOfDefinition [IsAdicRing A]
    (hA : ∃ I : Ideal A, I.FG ∧ Ideal.IsIdealOfDefinition I) :
    ∃ J : Ideal (weakIdealCompletion A A'), J.FG ∧ Ideal.IsIdealOfDefinition J :=
  sorry

/-- The weak-ideal completion of a Noetherian algebra over a Noetherian adic ring is
Noetherian. -/
instance instIsNoetherianRing [IsAdicRing A] [IsNoetherianRing A]
    [IsNoetherianRing A'] : IsNoetherianRing (weakIdealCompletion A A') := sorry

/-- The weak-ideal completion of a Noetherian algebra over a Noetherian adic ring is
both adic and Noetherian. -/
theorem isAdicRing_and_isNoetherianRing [IsAdicRing A] [IsNoetherianRing A]
    [IsNoetherianRing A'] :
    IsAdicRing (weakIdealCompletion A A') ∧ IsNoetherianRing (weakIdealCompletion A A') := by
  obtain ⟨I, hI⟩ := IsPreadmissibleRing.exists_ideal_isIdealOfDefinition (R := A)
  exact ⟨isAdicRing ⟨I, IsNoetherian.noetherian I, hI⟩, instIsNoetherianRing⟩

end TopologicalRing.weakIdealCompletion
