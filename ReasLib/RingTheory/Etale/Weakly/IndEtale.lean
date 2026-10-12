/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Etale.Weakly
public import ReasLib.RingTheory.RingHom.IndEtale.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Ind-etale algebras are weakly etale

This leaf owns the base-ring-independent direction of the ind-etale/weakly-etale
comparison.  Field hypotheses belong only to the converse in `Weakly.Field`.
@stack 092N
-/

@[expose] public section

universe u v

namespace Algebra.WeaklyEtale

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An ind-etale algebra map is weakly etale over an arbitrary commutative base ring. -/
@[stacks 092N "ind-etale algebras are weakly etale"]
theorem of_indEtale (h : (algebraMap R S).IndEtale) :
    Algebra.WeaklyEtale R S := sorry

end Algebra.WeaklyEtale
