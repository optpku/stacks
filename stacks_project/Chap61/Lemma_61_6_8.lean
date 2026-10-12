/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Topology.ExtremallyDisconnected
public import stacks_project.Chap61.Definition_61_4_1_IndZariski
public import stacks_project.Chap61.Lemma_61_6_7
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.6.8

Every commutative ring admits a faithfully flat ind-Zariski extension whose
target satisfies the equivalent conditions of Lemma 61.6.7.
-/

@[expose] public section

universe u

open Algebra

namespace RingHom.IndZariski

/-- Lemma 61.6.8: for a commutative ring `A`, there exists a faithfully flat
ind-Zariski ring map `f : A →+* B` such that `B` satisfies the equivalent
conditions of Lemma 61.6.7. -/
@[stacks 09B0]
theorem exists_faithfullyFlat_indZariskiRetraction (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      f.FaithfullyFlat ∧ f.IndZariski ∧ HasFaithfullyFlatIndZariskiRetraction B :=
  sorry

/-- There exists a faithfully flat ind-Zariski ring map `f : A →+* B` such that
`PrimeSpectrum B` is w-local and `ConnectedComponents (PrimeSpectrum B)` is
extremally disconnected. -/
theorem exists_faithfullyFlat_wLocal_extremallyDisconnected
    (A : Type u) [CommRing A] :
    ∃ (B : Type u) (_ : CommRing B) (f : A →+* B),
      f.FaithfullyFlat ∧ f.IndZariski ∧
        WLocalSpace (PrimeSpectrum B) ∧
          ExtremallyDisconnected (ConnectedComponents (PrimeSpectrum B)) :=
  sorry

end RingHom.IndZariski
