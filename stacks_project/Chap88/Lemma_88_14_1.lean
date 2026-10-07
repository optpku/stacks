module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Lemma_88_14_1_RigClosed

/-!
# Lemma 88.14.1

Eight equivalent characterizations of rig-closed primes of a Noetherian adic
topological ring.
-/

@[expose] public section

universe u

open Ideal.IsRigClosed

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

/-- Lemma 88.14.1: for a Noetherian adic topological ring `A` and a prime
`q ⊂ A`, the following are equivalent: maximality among primes not containing
some topological ideal of definition `I`; `q` is a closed point of
`PrimeSpectrum A` minus `zeroLocus I` for some such `I`; the same two
conditions for every topological ideal of definition; `ringKrullDim (A ⧸ q) = 1`
with `I ⊈ q` for some such `I`; dimension 1 with this avoidance for every such
`I`; dimension 1 with nontrivial induced topology on `A ⧸ q`; and `A ⧸ q` is a
1-dimensional Noetherian complete local domain whose maximal ideal is the
radical of the image of any topological ideal of definition of `A`. -/
@[stacks 0GG8]
theorem PrimeSpectrum.isRigClosed_tfae (q : PrimeSpectrum A) :
    List.TFAE
      [ existsMaximal q.asIdeal, existsClosedPoint q
      , forallMaximal q.asIdeal, forallClosedPoint q
      , dimOneExistsNotLe q.asIdeal, dimOneForallNotLe q.asIdeal
      , dimOneNontrivialTopology q.asIdeal
      , isCompleteLocalDomain q.asIdeal ] :=
  sorry
