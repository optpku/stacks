/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.Unramified.LocalStructure
import StacksCheckRecall

/-!
@stack 00U5

# Etale Maps Are Quasi-Finite

Lemma 10.143.6 is the canonical `Algebra.QuasiFinite` instance supplied by an
etale algebra.
-/

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable [Algebra.Etale R S]

/- Lemma 10.143.6: an etale ring map `R → S` is quasi-finite.  The algebra-level
statement is already a canonical instance, and `RingHom.quasiFinite_algebraMap`
is the bridge to the source's ring-map wording. -/
#synth Algebra.QuasiFinite R S
@[stacks 00U5 "etale ring-map quasi-finiteness"]
#check @RingHom.quasiFinite_algebraMap

end
