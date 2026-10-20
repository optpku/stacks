/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

@[expose] public section

/-!
# Henselizations of ring pairs

@stack 0AH5

`IsPairHenselization B J A I` is the intrinsic owner predicate for a henselization
of the pair `(B, J)`.  It records the henselian target, the ind-etale map, and
the exact closed-fiber comparison; a chosen categorical construction is not
part of the reusable API.
-/

universe u v

/-- A pair `(A, I)` is a henselization of `(B, J)` when its structural map is
ind-etale, carries `J` onto `I`, and induces an isomorphism on the quotients. -/
@[stacks 0AH5 "henselization of a ring pair"]
class IsPairHenselization
    (B : Type u) [CommRing B] (J : Ideal B)
    (A : Type v) [CommRing A] [Algebra B A] (I : Ideal A) : Prop
    extends HenselianRing A I where
  /-- The distinguished ideal is the image of the base ideal. -/
  map_ideal : Ideal.map (algebraMap B A) J = I
  /-- The induced map on closed fibers is bijective. -/
  quotient_bijective :
    Function.Bijective
      (Ideal.quotientMap I (algebraMap B A)
        (Ideal.map_le_iff_le_comap.mp map_ideal.le))
  /-- The structural map is ind-etale. -/
  indEtale : RingHom.IndEtale (algebraMap B A)

namespace IsPairHenselization

variable {B : Type u} [CommRing B] {J : Ideal B}
variable {A : Type v} [CommRing A] [Algebra B A] {I : Ideal A}

/-- The base ideal maps into the distinguished ideal of a pair
henselization. -/
theorem le_comap_ideal [IsPairHenselization B J A I] :
    J ≤ Ideal.comap (algebraMap B A) I := sorry

/-- The henselian, ideal, quotient, and ind-etale clauses of a pair
henselization, exposed together for downstream proofs. -/
@[stacks 0AH5 "pair henselization specification"]
theorem spec [IsPairHenselization B J A I] :
    HenselianRing A I ∧
      Ideal.map (algebraMap B A) J = I ∧
        J ≤ Ideal.comap (algebraMap B A) I ∧
          Function.Bijective
            (Ideal.quotientMap I (algebraMap B A)
              (IsPairHenselization.le_comap_ideal (B := B) (J := J) (A := A)
                (I := I))) ∧
            RingHom.IndEtale (algebraMap B A) := sorry

/-- A pair henselization of a Noetherian base ring is Noetherian. -/
@[stacks 0AH5 "Noetherian pair henselization"]
theorem isNoetherianRing
    [IsPairHenselization B J A I] [IsNoetherianRing B] : IsNoetherianRing A := sorry

end IsPairHenselization
