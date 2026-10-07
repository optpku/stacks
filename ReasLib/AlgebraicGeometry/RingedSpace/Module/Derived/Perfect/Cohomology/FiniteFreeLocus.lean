module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# The finite-free cohomology locus of a perfect derived module

For a perfect derived module over a ringed space with local stalk rings, the pointwise
finite-free locus is open. This leaf owns that open subset and its maximality characterization.
-/

open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- Lemma 20.49.11 (1): the locus where all cohomology stalks of a perfect derived module are
finite free is open when the stalk rings are local. -/
@[stacks 0GT1 "(1)"]
theorem IsPerfect.isOpen_finiteFreeLocus
    {E : ModuleDerived X} (hE : IsPerfect E)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    IsOpen (Cohomology.finiteFreeLocus E) := sorry

/-- The open subset where all cohomology stalks of a perfect derived module are finite free. -/
@[stacks 0GT1 "finite-free cohomology open"]
def IsPerfect.finiteFreeOpen
    {E : ModuleDerived X} (hE : IsPerfect E)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) : Opens X.carrier :=
  ⟨Cohomology.finiteFreeLocus E, hE.isOpen_finiteFreeLocus h_local⟩

/-- The carrier of `hE.finiteFreeOpen h_local` is the finite-free cohomology locus. -/
@[simp]
theorem IsPerfect.coe_finiteFreeOpen
    {E : ModuleDerived X} (hE : IsPerfect E)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    (hE.finiteFreeOpen h_local : Set X) = Cohomology.finiteFreeLocus E := sorry

/-- A point belongs to `hE.finiteFreeOpen h_local` exactly when every cohomology stalk there is
finite free. -/
@[simp]
theorem IsPerfect.mem_finiteFreeOpen_iff
    {E : ModuleDerived X} (hE : IsPerfect E)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) (x : X) :
    x ∈ hE.finiteFreeOpen h_local ↔
      ∀ i : ℤ, cohomologyStalkFiniteFree E i x := sorry

/-- All cohomology sheaves become finite locally free on the finite-free cohomology open. -/
theorem IsPerfect.finiteLocallyFreeOn_finiteFreeOpen
    {E : ModuleDerived X} (hE : IsPerfect E)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) :
    Cohomology.finiteLocallyFreeOn E (hE.finiteFreeOpen h_local) := sorry

/-- Lemma 20.49.11 (2): the finite-free cohomology open is the maximal open subset on which all
cohomology sheaves are finite locally free. -/
@[stacks 0GT1 "(2)"]
theorem IsPerfect.finiteLocallyFreeOn_iff_le_finiteFreeOpen
    {E : ModuleDerived X} (hE : IsPerfect E)
    (h_local : ∀ x : X, IsLocalRing (X.presheaf.stalk x)) (U : Opens X.carrier) :
    Cohomology.finiteLocallyFreeOn E U ↔ U ≤ hE.finiteFreeOpen h_local := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
