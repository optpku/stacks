/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime Localizations under Universe Lift

@stack 0523

This leaf records the canonical transport of a prime ideal and its local ring
through `ULift.ringEquiv`.  Its final section packages the compatible lifted
prime fiber of an arbitrary algebra map without tying the API to a particular
subalgebra presentation.
-/

@[expose] public section

universe u v w

namespace ULift

variable {A : Type u} [CommSemiring A]

/-- Tag `0523`: the contraction of an ideal along the canonical universe-lift ring
equivalence. -/
@[stacks 0523 "prime ideals under universe lift"]
abbrev comapIdeal (Q : Ideal A) : Ideal (ULift.{v} A) :=
  Q.comap (ULift.ringEquiv : ULift.{v} A ≃+* A)

/-- Tag `0523`: the contraction of a prime ideal along `ULift.ringEquiv` is prime. -/
@[stacks 0523 "prime ideals under universe lift"]
instance comapIdeal_isPrime (Q : Ideal A) [Q.IsPrime] :
    (comapIdeal.{u, v} Q).IsPrime :=
  Ideal.comap_isPrime ((ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom) Q

/-- Tag `0523`: localizing a universe-lifted ring at the contracted prime is canonically
equivalent to localizing the original ring. -/
@[stacks 0523 "prime localizations under universe lift"]
noncomputable def atPrimeEquiv (Q : Ideal A) [Q.IsPrime] :
    Localization.AtPrime (comapIdeal.{u, v} Q) ≃+* Localization.AtPrime Q :=
  IsLocalization.ringEquivOfRingEquiv
    (Localization.AtPrime (comapIdeal.{u, v} Q))
    (Localization.AtPrime Q)
    (ULift.ringEquiv : ULift.{v} A ≃+* A)
    ((ULift.ringEquiv : ULift.{v} A ≃+* A).map_primeCompl_comap_eq Q)

/-- Tag `0523`: `atPrimeEquiv` sends a dense coefficient class to the class
of its image under `ULift.ringEquiv`. -/
@[simp, stacks 0523 "prime localizations under universe lift"]
theorem atPrimeEquiv_apply_algebraMap (Q : Ideal A) [Q.IsPrime]
    (a : ULift.{v} A) :
    atPrimeEquiv Q
        (algebraMap (ULift.{v} A)
          (Localization.AtPrime (comapIdeal.{u, v} Q)) a) =
      algebraMap A (Localization.AtPrime Q)
        ((ULift.ringEquiv : ULift.{v} A ≃+* A) a) := sorry

/-- Tag `0523`: the universe-lift localization equivalence is the canonical local-ring map
induced by `ULift.ringEquiv`. -/
@[stacks 0523 "prime localizations under universe lift"]
theorem atPrimeEquiv_apply (Q : Ideal A) [Q.IsPrime]
    (y : Localization.AtPrime (comapIdeal.{u, v} Q)) :
    atPrimeEquiv Q y =
      Localization.localRingHom (comapIdeal.{u, v} Q) Q
        ((ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom) rfl y := sorry

end ULift

namespace ULift

variable {R : Type u} {A : Type v} {S : Type w}
variable [CommSemiring R] [CommSemiring A] [CommSemiring S]
variable [Algebra R A] [Algebra R S]

/-- Tag `0523`: after contracting a prime ideal along an `R`-algebra map and lifting both
the base and source rings, the resulting prime ideal lies over the lifted contraction to `R`. -/
@[stacks 0523 "prime fibers under universe lift"]
theorem comapIdeal_liesOver
    (f : A →ₐ[R] S) (q : Ideal S) [q.IsPrime] :
    letI : Algebra (ULift.{v} R) (ULift.{u} A) :=
      ULift.algebra' R (ULift.{u} A)
    (ULift.comapIdeal.{v, u} (Ideal.comap f.toRingHom q)).LiesOver
      (ULift.comapIdeal.{u, v} (q.under R)) := sorry

/-- Tag `0523`: the prime obtained by contracting `q` along an `R`-algebra map is a distinguished
point of the lifted fiber over the contraction of `q` to `R`. -/
@[stacks 0523 "prime fibers under universe lift"]
noncomputable def comapPrimeOver
    (f : A →ₐ[R] S) (q : Ideal S) [q.IsPrime] :
    letI : Algebra (ULift.{v} R) (ULift.{u} A) :=
      ULift.algebra' R (ULift.{u} A)
    (ULift.comapIdeal.{u, v} (q.under R)).primesOver (ULift.{u} A) :=
  -- Local instance justification (instance diamond): Mathlib intentionally keeps
  -- `ULift.algebra'` non-global, while this canonical lifted fiber needs that precise action.
  letI : Algebra (ULift.{v} R) (ULift.{u} A) :=
    ULift.algebra' R (ULift.{u} A)
  letI : (ULift.comapIdeal.{v, u} (Ideal.comap f.toRingHom q)).LiesOver
      (ULift.comapIdeal.{u, v} (q.under R)) :=
    comapIdeal_liesOver f q
  Ideal.primesOver.mk
    (ULift.comapIdeal.{u, v} (q.under R))
    (ULift.comapIdeal.{v, u} (Ideal.comap f.toRingHom q))

/-- Tag `0523`: the underlying ideal of `comapPrimeOver` is the lifted contraction of `q` along
the given algebra map. -/
@[simp, stacks 0523 "prime fibers under universe lift"]
theorem comapPrimeOver_asIdeal
    (f : A →ₐ[R] S) (q : Ideal S) [q.IsPrime] :
    letI : Algebra (ULift.{v} R) (ULift.{u} A) :=
      ULift.algebra' R (ULift.{u} A)
    (comapPrimeOver f q).1 =
      ULift.comapIdeal.{v, u} (Ideal.comap f.toRingHom q) := sorry

/-- Tag `0523`: the distinguished lifted prime `comapPrimeOver f q` contracts to the lifted
contraction of `q` on the base ring. -/
@[stacks 0523 "prime fibers under universe lift"]
theorem comapPrimeOver_under_eq
    (f : A →ₐ[R] S) (q : Ideal S) [q.IsPrime] :
    letI : Algebra (ULift.{v} R) (ULift.{u} A) :=
      ULift.algebra' R (ULift.{u} A)
    Ideal.comap (algebraMap (ULift.{v} R) (ULift.{u} A))
        ((comapPrimeOver f q).1) =
      ULift.comapIdeal.{u, v} (q.under R) := sorry

end ULift
