/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.RegularSequence
public import ReasLib.RingTheory.Ideal.Cotangent.Generation

@[expose] public section

/-!
# Cotangent Generators and Regular Sequences

@stack 00SC

This leaf combines the ideal-theoretic cotangent-generation bridge with the
local Cohen--Macaulay expected-codimension criterion.
-/

universe u

namespace Ideal.Cotangent

variable {R : Type u} [CommRing R]

/-- A regular sequence indexed by `Fin c` which generates an ideal gives a basis of the
cotangent module `I / I²` represented by the images of its chosen generators. -/
@[stacks 00SC "regular generators give a cotangent basis"]
theorem exists_basis_of_isRegular_of_span_eq
    {I : Ideal R} {c : ℕ} (xs : Fin c → I)
    (hreg : RingTheory.Sequence.IsRegular R (List.ofFn fun i => (xs i : R)))
    (hxs : Ideal.span (Set.range fun i => (xs i : R)) = I) :
    ∃ b : Module.Basis (Fin c) (R ⧸ I) I.Cotangent,
      ∀ i, b i = I.toCotangent (xs i) := sorry

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [Module.CohenMacaulay R R]

/-- Lemma 10.135.4 (Stacks tag `00SC`), corrected terminal assertion: if `c` specified
elements of a local ideal generate `I / I²` and the quotient has codimension `c`, then those
elements form a regular sequence.

The family is indexed by `Fin c` so the codimension and sequence length agree definitionally. -/
@[stacks 00SC "cotangent generators form a regular sequence"]
theorem isRegular_of_span_toCotangent_eq_top
    {I : Ideal R} {c : ℕ} (xs : Fin c → I)
    (hI : I ≤ IsLocalRing.maximalIdeal R)
    (hxs : Submodule.span (R ⧸ I) (Set.range fun i => I.toCotangent (xs i)) = ⊤)
    (hdim : ringKrullDim (R ⧸ I) + c = ringKrullDim R) :
    RingTheory.Sequence.IsRegular R (List.ofFn fun i => (xs i : R)) := sorry

end Ideal.Cotangent
