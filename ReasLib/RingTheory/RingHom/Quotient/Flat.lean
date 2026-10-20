module

public import Mathlib.Data.PNat.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.RingTheory.RingHom.Quotient
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat quotient maps along ideal powers

This leaf records the induction-stable quotient comparison attached to a flat ring homomorphism.
It is independent of Ext and is therefore reusable by tensor, torsion, and completion arguments.
@stack 05E9
-/

@[expose] public section

universe u v

namespace RingHom.Flat

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Lemma 15.90.2 (Tag 05E9): a flat ring map inducing a bijection modulo `I` induces a
bijection modulo every positive power of `I`. -/
@[stacks 05E9]
theorem quotientByIdeal_pow_bijective (f : R →+* S) (hf : f.Flat)
    (I : Ideal R) (hquot : Function.Bijective (f.quotientByIdeal I)) (n : ℕ+) :
    Function.Bijective (f.quotientByIdeal (I ^ (n : ℕ))) := sorry

end RingHom.Flat
