module

public import ReasLib.AlgebraicGeometry.RelativeCycle.Hilbert
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Cycle classes of Hilbert points

This file preserves the source-facing typed compatibility surface for the
shared relative-cycle Hilbert API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- A typed compatibility check for the subgroup-valued Hilbert cycle-class map. -/
#check (AlgebraicGeometry.RelativeCycle.cycleClassHomToGroup :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [f.FiniteType] (r : ℕ),
    FreeAbelianGroup (AlgebraicGeometry.RelativeCycle.Hilb f r) →+
      AlgebraicGeometry.RelativeCycle.group f r)
