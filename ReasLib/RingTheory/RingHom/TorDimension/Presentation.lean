module

public import ReasLib.RingTheory.Extension.Presentation.SquareZero
public import ReasLib.RingTheory.RingHom.Perfect.TorDimension

@[expose] public section

/-!
# Presentation obstructions to finite Tor dimension

The presentation-level `LiftedRelation` and its obstruction class live in
`ReasLib.RingTheory.Extension.Presentation.SquareZero`.  This file records only the downstream
consequences of a nonnilpotent obstruction for Tor dimension and perfectness.
-/

noncomputable section

open scoped BigOperators

universe u' u v w t

namespace Algebra.Presentation

variable {R' : Type u'} {R : Type u} {S : Type v}
variable [CommRing R'] [CommRing R] [CommRing S] [Algebra R S]
variable {f : R' →+* R} [f.IsSquareZeroExtension]
variable {g : RingHom.SquareZeroExtension.Generator f}
variable {ι : Type w} {σ : Type t} [Fintype σ]

namespace LiftedRelation

variable {P : Presentation R S ι σ}

/-- Lemma 23.7.3 (Tag 09PU): a nonnilpotent lifted-relation obstruction
prevents the presented algebra from having finite Tor dimension. -/
@[stacks 09PU]
theorem not_hasFiniteTorDimension [IsNoetherianRing R'] [IsNoetherianRing R]
    (L : LiftedRelation g P) (hL : ¬ IsNilpotent L.obstruction) :
    ¬ (algebraMap R S).HasFiniteTorDimension := sorry

/-- A nonnilpotent lifted-relation obstruction prevents the presented
algebra map from being perfect. -/
@[stacks 09PU "perfect-map consequence"]
theorem not_isPerfectRingMap [IsNoetherianRing R'] [IsNoetherianRing R]
    (L : LiftedRelation g P) (hL : ¬ IsNilpotent L.obstruction) :
    ¬ (algebraMap R S).IsPerfectRingMap := sorry

end LiftedRelation

end Algebra.Presentation
