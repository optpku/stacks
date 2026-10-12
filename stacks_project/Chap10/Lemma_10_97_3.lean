/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Completion.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

/-!
@stack 00MC

# Faithful flatness of completion
-/

universe u

open IsLocalRing

namespace AdicCompletion

section jacobson

variable {R : Type u} [CommRing R] [IsNoetherianRing R]
variable (I : Ideal R) (hI : I ≤ Ring.jacobson R)

/- Lemma 10.97.3 (1): completion along an ideal contained in the Jacobson
radical of a Noetherian ring is faithfully flat. -/
@[stacks 00MC "(1)"]
#check (algebraMap_faithfullyFlat I hI :
  RingHom.FaithfullyFlat (algebraMap R (AdicCompletion I R)))

end jacobson

section localRing

variable (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/- Lemma 10.97.3 (2): in particular, completion of a Noetherian local ring
along its maximal ideal is faithfully flat. -/
@[stacks 00MC "(2)"]
#check (maximalIdeal_algebraMap_faithfullyFlat R :
  RingHom.FaithfullyFlat
    (algebraMap R (AdicCompletion (maximalIdeal R) R)))

end localRing
end AdicCompletion

#check @adicCompletion_algebraMap_faithfullyFlat_of_le_jacobson
#check @maximalIdeal_adicCompletion_algebraMap_faithfullyFlat
