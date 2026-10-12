/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalIso

@[expose] public section

universe u

namespace Algebra.IsLocalIso

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalIso R S]

/- Lemma 61.3.5 (1): if `algebraMap R S` is a local isomorphism, then it is étale. -/
@[stacks 096I] #check (Algebra.IsLocalIso.etale : Algebra.Etale R S)

/- Lemma 61.3.5 (2): if `algebraMap R S` is a local isomorphism, then it identifies
local rings. -/
@[stacks 096I]
#check (Algebra.IsLocalIso.isIsoOnLocalRings :
  RingHom.IsIsoOnLocalRings (algebraMap R S))

/- Lemma 61.3.5 (3): if `algebraMap R S` is a local isomorphism, then it is
quasi-finite in the finite-type sense of `Algebra.FiniteType.QuasiFinite`. -/
@[stacks 096I]
#check (Algebra.IsLocalIso.finiteType_quasiFinite : Algebra.FiniteType.QuasiFinite R S)

end Algebra.IsLocalIso
