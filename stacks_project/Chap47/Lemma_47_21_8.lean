/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.RingTheory.Gorenstein.FlatLocal

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B] [Module.Flat A B]

/- Lemma 47.21.8 -/
@[stacks 0BJL] #check
  (IsGorensteinLocalRing.target_iff_source_and_closedFiber :
    IsGorensteinLocalRing B ↔
      IsGorensteinLocalRing A ∧
        IsGorensteinLocalRing ((IsLocalRing.maximalIdeal A).Fiber B))

end
