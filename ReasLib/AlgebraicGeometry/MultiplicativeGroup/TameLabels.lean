/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.MultiplicativeGroup.TameGeometry

/-! Canonical Frobenius labels as actual nonempty conjugacy orbits, without selecting a path. -/

@[expose] public section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme TopologicalSpace
noncomputable section
universe u v

namespace MultiplicativeGroupTame

/-- A conjugacy class represented by its actual carrier, with no selected representative. -/
structure ConjugacyOrbit (G : Type u) [Group G] where
  carrier : Set G
  nonempty : carrier.Nonempty
  mem_iff {g h : G} : g ∈ carrier → (h ∈ carrier ↔ IsConj g h)

namespace ConjugacyOrbit
variable {G : Type u} [Group G]

instance : SetLike (ConjugacyOrbit G) G where
  coe := ConjugacyOrbit.carrier
  coe_injective a b h := by cases a; cases b; cases h; rfl

/-- The canonical orbit projection has the explicit conjugacy predicate as carrier. -/
def ofElement (g : G) : ConjugacyOrbit G where
  carrier := {h | IsConj g h}
  nonempty := ⟨g, IsConj.refl g⟩
  mem_iff := fun hgh ↦ ⟨fun hgi ↦ hgh.symm.trans hgi, fun hhi ↦ hgh.trans hhi⟩

theorem mem_ofElement (g h : G) : h ∈ ofElement g ↔ IsConj g h := Iff.rfl

end ConjugacyOrbit

variable (k : Type u) [Field k] [Finite k] (η : GeometricPoint (space k))

/-- The carrier consists of the concrete local Frobenius transported along EVERY actual path. -/
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

/-- A total canonical label, with actual carrier and only property proofs deferred. -/
def frobeniusLabel (x : closedPoints (overField k).left) : ConjugacyOrbit (fundamentalGroup k η) where
  carrier := frobeniusOrbitCarrier k η x
  nonempty := frobeniusOrbitCarrier_nonempty k η x
  mem_iff := frobeniusOrbitCarrier_mem_iff k η x

theorem frobeniusLabel_mem (x : closedPoints (overField k).left) (g : fundamentalGroup k η) :
    g ∈ frobeniusLabel k η x ↔
      ∃ t : fiber k (pointOver k x) ≅ fiber k η, g = frobeniusAlong k η x t := Iff.rfl

/-- The source's full positive-degree point family has a total actual label function. -/
def labels (d : ℕ+) : points k d → ConjugacyOrbit (fundamentalGroup k η) :=
  fun x ↦ frobeniusLabel k η x.val

/-- Comparison with the quotient representation is a conclusion with its projection pinned.
It is not chosen to construct either the orbit or the label. -/
theorem exists_quotient_comparison :
    ∃ e : ConjugacyOrbit (fundamentalGroup k η) ≃ ConjClasses (fundamentalGroup k η),
      ∀ g, e (ConjugacyOrbit.ofElement g) = ConjClasses.mk g := by
  sorry

/-- Every representative of the actual degree-d orbit has numerical degree d. -/
theorem label_degree (p : ℕ) [Fact p.Prime] (ηp : GeometricPoint (space (ZMod p)))
    (d : ℕ+) (x : points (ZMod p) d) (g : fundamentalGroup (ZMod p) ηp)
    (hg : g ∈ labels (ZMod p) ηp d x) : degreeToIntegers p ηp g = integerNat d.val := by
  obtain ⟨t, rfl⟩ := hg
  exact frobeniusAlong_degree p ηp d x t

end MultiplicativeGroupTame
