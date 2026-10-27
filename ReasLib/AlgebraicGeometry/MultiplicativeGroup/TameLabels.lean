/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameGeometry

/-! Canonical Frobenius labels as actual nonempty conjugacy orbits, without selecting a path. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace
noncomputable section
open ProfiniteGrp (hatZ hatZNatCast)
universe u v

namespace MultiplicativeGroupTame

/-- A conjugacy class represented by its actual carrier, with no selected representative. -/
structure ConjugacyOrbit (G : Type u) [Group G] where
  /-- The elements in the conjugacy orbit. -/
  carrier : Set G
  /-- Every conjugacy orbit has a representative. -/
  nonempty : carrier.Nonempty
  /-- Relative to any representative, membership is precisely conjugacy. -/
  mem_iff {g h : G} : g ∈ carrier → (h ∈ carrier ↔ IsConj g h)

namespace ConjugacyOrbit
variable {G : Type u} [Group G]

/-- The canonical orbit projection has the explicit conjugacy predicate as carrier. -/
def ofElement (g : G) : ConjugacyOrbit G where
  carrier := {h | IsConj g h}
  nonempty := ⟨g, IsConj.refl g⟩
  mem_iff := fun hgh ↦ ⟨fun hgi ↦ hgh.symm.trans hgi, fun hhi ↦ hgh.trans hhi⟩

/-- The orbit of an element consists precisely of the elements conjugate to it. -/
theorem mem_ofElement (g h : G) : h ∈ (ofElement g).carrier ↔ IsConj g h := Iff.rfl

end ConjugacyOrbit

variable (k : Type u) [Field k] [Finite k] (η : GeometricPoint (space k))

/-- The set of local Frobenius elements transported along all paths to the base point. -/
def frobeniusOrbitCarrier (x : closedPoints (overField k).left) :
    Set (fundamentalGroup k η) :=
  {g | ∃ t : fiber k (pointOver k x) ≅ fiber k η, g = frobeniusAlong k η x t}

/-- Path existence for the connected tame Galois category makes this concrete set nonempty. -/
theorem frobeniusOrbitCarrier_nonempty (x : closedPoints (overField k).left) :
    (frobeniusOrbitCarrier k η x).Nonempty := by
  sorry

/-- Paths form a torsor under fiber automorphisms, so their images are exactly one conjugacy orbit. -/
theorem frobeniusOrbitCarrier_mem_iff (x : closedPoints (overField k).left)
    {g h : fundamentalGroup k η} (hg : g ∈ frobeniusOrbitCarrier k η x) :
    h ∈ frobeniusOrbitCarrier k η x ↔ IsConj g h := by
  sorry

/-- The Frobenius conjugacy orbit of a closed point, defined using all paths to the base point. -/
def frobeniusLabel (x : closedPoints (overField k).left) : ConjugacyOrbit (fundamentalGroup k η) where
  carrier := frobeniusOrbitCarrier k η x
  nonempty := frobeniusOrbitCarrier_nonempty k η x
  mem_iff := frobeniusOrbitCarrier_mem_iff k η x

/-- An element lies in the Frobenius orbit exactly when some path transports local Frobenius to it. -/
theorem frobeniusLabel_mem (x : closedPoints (overField k).left) (g : fundamentalGroup k η) :
    g ∈ (frobeniusLabel k η x).carrier ↔
      ∃ t : fiber k (pointOver k x) ≅ fiber k η, g = frobeniusAlong k η x t := Iff.rfl

/-- Assign to each positive-degree closed point its Frobenius conjugacy orbit. -/
def labels (d : ℕ+) : points k d → ConjugacyOrbit (fundamentalGroup k η) :=
  fun x ↦ frobeniusLabel k η x.val

/-- Conjugacy orbits are equivalent to quotient conjugacy classes, sending the orbit of an
element to its quotient class. -/
theorem exists_quotient_comparison :
    ∃ e : ConjugacyOrbit (fundamentalGroup k η) ≃ ConjClasses (fundamentalGroup k η),
      ∀ g, e (ConjugacyOrbit.ofElement g) = ConjClasses.mk g := by
  sorry

/-- Every representative of the actual degree-d orbit has numerical degree d. -/
theorem label_degree (p : ℕ) [Fact p.Prime] (ηp : GeometricPoint (space (ZMod p)))
    (d : ℕ+) (x : points (ZMod p) d) (g : fundamentalGroup (ZMod p) ηp)
    (hg : g ∈ (labels (ZMod p) ηp d x).carrier) : degreeToIntegers p ηp g = hatZNatCast d.val := by
  obtain ⟨t, rfl⟩ := hg
  exact frobeniusAlong_degree p ηp d x t

end MultiplicativeGroupTame
