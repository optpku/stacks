/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic
public import ReasLib.RingTheory.RingHom.TorDimension

/-!
# Perfect ring maps

The intrinsic definition combines pseudo-coherence with finite Tor dimension
of the target over the source.  Polynomial-presentation criteria live in the
separate `Perfect.Presentation` leaf.

@stack 067H
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v

namespace RingHom

/-- A commutative ring map is perfect when it is pseudo-coherent and its target has finite Tor
dimension over the source. -/
@[stacks 067H "Definition 15.83.1 (2), perfect ring map"]
class IsPerfectRingMap
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) : Prop extends
    IsPseudoCoherentRingMap f where
  /-- The target, regarded as a module over the source, has finite Tor dimension. -/
  finiteTorDimension : f.HasFiniteTorDimension

/-- A ring map is perfect exactly when it is pseudo-coherent and has finite Tor dimension. -/
theorem isPerfectRingMap_iff
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] (f : A →+* B) :
    f.IsPerfectRingMap ↔ f.IsPseudoCoherentRingMap ∧ f.HasFiniteTorDimension := sorry
/- Proof strategy: unfold the extending class, project `toIsPseudoCoherentRingMap` and
`finiteTorDimension` in one direction, and apply `IsPerfectRingMap.mk` in the other. -/

/-- The identity homomorphism of a commutative ring is perfect. -/
instance instIsPerfectRingMapId (A : Type u) [CommRing A] :
    (RingHom.id A).IsPerfectRingMap := sorry
/- Proof strategy: combine `RingHom.instIsPseudoCoherentRingMapId` with the zero Tor-dimension
bound for restriction along the identity ring homomorphism, then use `isPerfectRingMap_iff`. -/

end RingHom
