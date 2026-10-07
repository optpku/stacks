module

public import ReasLib.RingTheory.QuasiFinite.FiniteType
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.122.5

The finite-type fiber criterion is the canonical Mathlib `Algebra.quasiFinite_iff`.

@stack 00PM
-/

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.FiniteType R S]

/- Lemma 10.122.5: for a finite type ring map `R → S`, quasi-finiteness is
equivalent to finiteness of every residue-field fiber. -/
@[stacks 00PM]
#check @Algebra.FiniteType.QuasiFinite.iff_quasiFinite

#check @Algebra.quasiFinite_iff

end
