/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.Local.MaximalIdeal

@[expose] public section

/-!
# Maps on completions of local rings

This file owns the map on maximal-ideal completions induced by a local ring
homomorphism.  The construction is independent of any chosen presentation or
chapter-level approximation argument.

@stack 0CAR
-/

noncomputable section

open Ideal IsLocalRing

universe u v w

namespace AdicCompletion

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [IsLocalRing A] [IsLocalRing B]

/-- The finite-level quotient map used to construct the map on maximal-ideal
completions. -/
@[stacks 0CAR "finite-stage map underlying a local completion map"]
def localQuotientMap (f : A →+* B) [IsLocalHom f] (n : ℕ) :
    AdicCompletion (maximalIdeal A) A →+* B ⧸ maximalIdeal B ^ n :=
  (Ideal.quotientMap (maximalIdeal B ^ n) f
      (RingHom.IsLocalHom.pow_maximalIdeal_le_comap f n)).comp
    (AdicCompletion.evalₐ (maximalIdeal A) n)

/-- The finite-level quotient maps induced by a local homomorphism are
compatible with the transition maps of the target completion. -/
@[stacks 0CAR "compatibility of finite-stage local completion maps"]
theorem localQuotientMap_compatible (f : A →+* B) [IsLocalHom f]
    {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal B) h).comp (localQuotientMap f n) =
      localQuotientMap f m := sorry

/-- The canonical map between maximal-ideal completions induced by a local
homomorphism of local rings. -/
@[stacks 0CAR "map on maximal-ideal completions"]
noncomputable def mapLocal (f : A →+* B) [IsLocalHom f] :
    AdicCompletion (maximalIdeal A) A →+* AdicCompletion (maximalIdeal B) B :=
  AdicCompletion.liftRingHom (maximalIdeal B) (localQuotientMap f)
    (localQuotientMap_compatible f)

/-- The explicit algebra structure on the target maximal-ideal completion induced by `mapLocal`.
This is deliberately not a global instance: a pair of completions can carry several relevant
local maps, so the scalar map must remain an explicit choice. -/
@[stacks 0CAR "algebra structure from a maximal-ideal completion map"]
noncomputable abbrev mapLocalAlgebra (f : A →+* B) [IsLocalHom f] :
    Algebra (AdicCompletion (maximalIdeal A) A) (AdicCompletion (maximalIdeal B) B) :=
  (mapLocal f).toAlgebra

/-- The structural map of `mapLocalAlgebra` is the canonical map on maximal-ideal completions. -/
@[stacks 0CAR "structural map of the explicit completion algebra"]
theorem algebraMap_mapLocalAlgebra (f : A →+* B) [IsLocalHom f] :
    @algebraMap
        (AdicCompletion (maximalIdeal A) A)
        (AdicCompletion (maximalIdeal B) B)
        _ _ (mapLocalAlgebra f) =
      mapLocal f := sorry

/-- Evaluating the completion map induced by a local homomorphism at a finite target stage
recovers its defining local quotient map. -/
@[stacks 0CAR "finite-stage evaluation of a maximal-ideal completion map"]
theorem evalₐ_comp_mapLocal (f : A →+* B) [IsLocalHom f] (n : ℕ) :
    (evalₐ (maximalIdeal B) n).toRingHom.comp (mapLocal f) = localQuotientMap f n := sorry

/-- The pointwise finite-stage evaluation formula for `mapLocal`. -/
@[stacks 0CAR "pointwise finite-stage evaluation of a local completion map"]
theorem evalₐ_mapLocal (f : A →+* B) [IsLocalHom f] (n : ℕ)
    (x : AdicCompletion (maximalIdeal A) A) :
    evalₐ (maximalIdeal B) n (mapLocal f x) = localQuotientMap f n x := sorry

/-- At a finite stage, `mapLocal` sends a Cauchy representative to the quotient class of the
image of its corresponding value. -/
@[stacks 0CAR "finite-stage evaluation on Cauchy representatives"]
theorem evalₐ_mapLocal_mk (f : A →+* B) [IsLocalHom f] (n : ℕ)
    (r : AdicCauchySequence (maximalIdeal A) A) :
    evalₐ (maximalIdeal B) n (mapLocal f (AdicCompletion.mk (maximalIdeal A) A r)) =
      Ideal.Quotient.mk (maximalIdeal B ^ n) (f (r.val n)) := sorry

/-- The map on maximal-ideal completions extends the original local
homomorphism. -/
@[stacks 0CAR "local completion map extends the original homomorphism"]
theorem mapLocal_comp (f : A →+* B) [IsLocalHom f] :
    (mapLocal f).comp (algebraMap A (AdicCompletion (maximalIdeal A) A)) =
      (algebraMap B (AdicCompletion (maximalIdeal B) B)).comp f := sorry

/-- The completion map induced by a local homomorphism sends a dense source element to the dense
image of its image. -/
@[simp, stacks 0CAR "local completion map on dense source elements"]
theorem mapLocal_apply_algebraMap (f : A →+* B) [IsLocalHom f] (a : A) :
    mapLocal f (algebraMap A (AdicCompletion (maximalIdeal A) A) a) =
      algebraMap B (AdicCompletion (maximalIdeal B) B) (f a) := sorry

/-- Maximal-ideal completion maps compose functorially along local ring homomorphisms. -/
@[stacks 0CAR "composition of maximal-ideal completion maps"]
theorem mapLocal_comp_mapLocal {C : Type w} [CommRing C] [IsLocalRing C]
    (f : A →+* B) (g : B →+* C) [IsLocalHom f] [IsLocalHom g] :
    (mapLocal g).comp (mapLocal f) = mapLocal (g.comp f) := sorry

/-- The maximal-ideal completion map of an identity local ring homomorphism is the identity. -/
@[stacks 0CAR "identity maximal-ideal completion map"]
theorem mapLocal_id (A : Type u) [CommRing A] [IsLocalRing A] :
    mapLocal (RingHom.id A) = RingHom.id (AdicCompletion (maximalIdeal A) A) := sorry

end AdicCompletion
