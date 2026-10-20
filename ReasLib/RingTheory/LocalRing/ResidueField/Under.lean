module

public import ReasLib.RingTheory.LocalRing.ResidueField.Map

/-!
# Residue-field maps from contracted primes

This leaf packages the canonical residue-field map associated to a prime ideal
of an algebra. Its source is the residue field of Mathlib's canonical
contraction `Ideal.under`.

@stack 02M0
-/

@[expose] public section

universe u v

namespace Ideal.ResidueField

/-- The canonical residue-field map from the contraction of a prime ideal. -/
@[stacks 02M0 "residue-field map from a contracted prime"]
noncomputable def mapUnder
    (R : Type u) {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    (q : Ideal S) [q.IsPrime] :
    (q.under R).ResidueField →+* q.ResidueField :=
  Ideal.ResidueField.map (q.under R) q (algebraMap R S) rfl

end Ideal.ResidueField
