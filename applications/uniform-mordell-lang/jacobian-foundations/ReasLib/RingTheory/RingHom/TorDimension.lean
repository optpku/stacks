module

public import ReasLib.Algebra.Category.ModuleCat.RingHom
public import ReasLib.Algebra.Category.ModuleCat.Tor.Vanishing
public import ReasLib.Algebra.RingHom.ULift

/-!
# Tor dimension of ring homomorphisms

The predicates are intrinsic uniform-vanishing conditions for the ordinary
`Tor` bifunctor.  Their target module is explicit data, so downstream
statements do not need a local `Algebra` instance or a chosen derived-tensor
model.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism has Tor dimension at most `d` when Tor of its target
against every source module vanishes above `d`. -/
def HasTorDimensionLE (f : R →+* S) (d : ℕ) : Prop :=
  ∀ N : ModuleCat (ULift.{max u v} R),
    CategoryTheory.ModuleCat.Tor.IsZeroAbove f.uliftMax.targetModule N d

/-- A ring homomorphism has finite Tor dimension when one uniform Tor-vanishing bound
works for its target against every source module. -/
@[stacks 067H "finite Tor dimension of a ring map"]
def HasFiniteTorDimension (f : R →+* S) : Prop :=
  ∃ d : ℕ, f.HasTorDimensionLE d

/-- Increasing a Tor-dimension bound preserves the bound. -/
theorem HasTorDimensionLE.mono {f : R →+* S} {d e : ℕ}
    (h : f.HasTorDimensionLE d) (hde : d ≤ e) :
    f.HasTorDimensionLE e := sorry

/-- A finite Tor-dimension witness is exactly a uniform finite bound. -/
theorem hasFiniteTorDimension_iff (f : R →+* S) :
    f.HasFiniteTorDimension ↔ ∃ d : ℕ, f.HasTorDimensionLE d := sorry

/-- A specified Tor-dimension bound gives finite Tor dimension. -/
theorem HasTorDimensionLE.hasFiniteTorDimension {f : R →+* S} {d : ℕ}
    (h : f.HasTorDimensionLE d) : f.HasFiniteTorDimension := sorry

/-- Finite Tor dimension supplies a uniform Tor-dimension bound. -/
theorem HasFiniteTorDimension.exists_bound {f : R →+* S}
    (h : f.HasFiniteTorDimension) :
    ∃ d : ℕ, f.HasTorDimensionLE d := sorry

/-- The identity ring homomorphism has Tor dimension at most zero. -/
theorem HasTorDimensionLE.id (R : Type u) [CommRing R] :
    (RingHom.id R).HasTorDimensionLE 0 := sorry

/-- Tor-dimension bounds add under composition of ring homomorphisms. -/
theorem HasTorDimensionLE.comp
    {T : Type w} [CommRing T] {f : R →+* S} {g : S →+* T} {d e : ℕ}
    (hf : f.HasTorDimensionLE d) (hg : g.HasTorDimensionLE e) :
    (g.comp f).HasTorDimensionLE (d + e) := sorry

/-- Finite Tor dimension is preserved by composition of ring homomorphisms. -/
theorem HasFiniteTorDimension.comp
    {T : Type w} [CommRing T] {f : R →+* S} {g : S →+* T}
    (hf : f.HasFiniteTorDimension) (hg : g.HasFiniteTorDimension) :
    (g.comp f).HasFiniteTorDimension := sorry

/-- A Tor-dimension bound for a ring map makes its target Tor vanish above
that bound against every source module. -/
theorem HasTorDimensionLE.torIsZeroAbove {f : R →+* S} {d : ℕ}
    (h : f.HasTorDimensionLE d)
    (N : ModuleCat (ULift.{max u v} R)) :
    CategoryTheory.ModuleCat.Tor.IsZeroAbove f.uliftMax.targetModule N d := sorry

/-- Finite Tor dimension of a ring map gives eventual Tor vanishing against
every source module. -/
theorem HasFiniteTorDimension.torEventuallyIsZero {f : R →+* S}
    (h : f.HasFiniteTorDimension)
    (N : ModuleCat (ULift.{max u v} R)) :
    CategoryTheory.ModuleCat.Tor.EventuallyIsZero f.uliftMax.targetModule N := sorry

end RingHom
