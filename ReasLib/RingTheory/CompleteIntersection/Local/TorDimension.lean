/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.JacobsonSpace
public import ReasLib.RingTheory.CompleteIntersection.Local
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import ReasLib.RingTheory.RingHom.TorDimension

/-!
# Local complete intersections and finite Tor dimension

This leaf relates absolute local-complete-intersection conditions across a
finite-type map to the relative local-complete-intersection condition.
-/

@[expose] public section

universe u v

open PrimeSpectrum Set

namespace RingHom

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]

namespace CompleteIntersection

namespace FiniteTorDimension

/-- Under the hypotheses of the finite-Tor criterion, a complete-intersection target and finite
Tor dimension force the source to be a local complete intersection. -/
theorem source_of_target (f : A →+* B) [IsNoetherianRing A]
    (hfinite : f.FiniteType)
    (hclosed : closedPoints (PrimeSpectrum A) ⊆ Set.range (PrimeSpectrum.comap f))
    (hB : IsLocalCompleteIntersectionRing B) (hTor : f.HasFiniteTorDimension) :
    IsLocalCompleteIntersectionRing A := sorry

/-- Under the hypotheses of the finite-Tor criterion, a complete-intersection target and finite
Tor dimension force the map to be a local complete intersection. -/
theorem relative_of_target (f : A →+* B) [IsNoetherianRing A]
    (hfinite : f.FiniteType)
    (hclosed : closedPoints (PrimeSpectrum A) ⊆ Set.range (PrimeSpectrum.comap f))
    (hB : IsLocalCompleteIntersectionRing B) (hTor : f.HasFiniteTorDimension) :
    f.IsLocalCompleteIntersection := sorry

/-- Under the hypotheses of the finite-Tor criterion, a complete-intersection source and a local
complete-intersection map force the target to be a local complete intersection. -/
theorem target_of_source (f : A →+* B) [IsNoetherianRing A]
    (hfinite : f.FiniteType)
    (hclosed : closedPoints (PrimeSpectrum A) ⊆ Set.range (PrimeSpectrum.comap f))
    (hA : IsLocalCompleteIntersectionRing A) (hf : f.IsLocalCompleteIntersection) :
    IsLocalCompleteIntersectionRing B := sorry

/-- Under the hypotheses of the finite-Tor criterion, a complete-intersection source and a local
complete-intersection map give finite Tor dimension. -/
theorem of_source_of_relative (f : A →+* B) [IsNoetherianRing A]
    (hfinite : f.FiniteType)
    (hclosed : closedPoints (PrimeSpectrum A) ⊆ Set.range (PrimeSpectrum.comap f))
    (hA : IsLocalCompleteIntersectionRing A) (hf : f.IsLocalCompleteIntersection) :
    f.HasFiniteTorDimension := sorry

/-- For a finite-type map from a Noetherian ring whose spectrum image contains
all closed points, the target is a local complete intersection and the map has
finite Tor dimension exactly when the source is a local complete intersection
and the map is a local complete intersection. -/
@[stacks 09QF]
theorem target_iff_source
    (f : A →+* B) [IsNoetherianRing A] (hfinite : f.FiniteType)
    (hclosed :
      closedPoints (PrimeSpectrum A) ⊆ Set.range (PrimeSpectrum.comap f)) :
    (IsLocalCompleteIntersectionRing B ∧ f.HasFiniteTorDimension) ↔
      (IsLocalCompleteIntersectionRing A ∧ f.IsLocalCompleteIntersection) := sorry

end FiniteTorDimension

end CompleteIntersection

end RingHom
