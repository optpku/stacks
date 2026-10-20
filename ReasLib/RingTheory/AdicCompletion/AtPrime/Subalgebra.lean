module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.LocalEquiv.Stage
public import ReasLib.RingTheory.Localization.AtPrime.Subalgebra

/-!
# Completed Prime Localizations of Subalgebras

@stack 00QR

This leaf lifts the basic-open comparison for a subalgebra from prime
localizations to their maximal-ideal completions.  The dense and finite-stage
formulas are kept separate so consumers can compose them with their own
localization or scalar-tower comparisons.
-/

@[expose] public section

open IsLocalRing

universe u v

namespace Subalgebra

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/-- Tag `00QR`: a bijective basic-open comparison from a subalgebra induces an equivalence
between the completions of the corresponding prime local rings. -/
@[stacks 00QR "completed subalgebra basic-open localization equivalence"]
noncomputable def completionEquivOfAwayMapBijective
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r : A) (hrq : (r : S) ∉ q)
    (h : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    AdicCompletion
        (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) ≃+*
      AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q) :=
  AdicCompletion.mapLocalEquiv (localRingEquivOfAwayMapBijective A r hrq h)

/-- Tag `00QR`: the completed basic-open comparison sends a dense local-ring image to the
dense image of its canonical local-ring comparison. -/
@[simp, stacks 00QR "completed subalgebra basic-open localization equivalence"]
theorem completionEquivOfAwayMapBijective_apply_algebraMap
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r : A) (hrq : (r : S) ∉ q)
    (h : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :
    completionEquivOfAwayMapBijective A r hrq h
        (algebraMap
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q))) x) =
      algebraMap
        (Localization.AtPrime q)
        (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))
        (localRingEquivOfAwayMapBijective A r hrq h x) := sorry

/-- The completed away-bijective comparison sends the canonical image of a subalgebra element
to the canonical image of the same ambient element. -/
@[stacks 00QR "completed subalgebra basic-open localization equivalence"]
theorem completionEquivOfAwayMapBijective_apply_of
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r a : A) (hrq : (r : S) ∉ q)
    (h : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    completionEquivOfAwayMapBijective A r hrq h
        (algebraMap
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q))
          (AdicCompletion
            (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
            (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
          (algebraMap A (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) a)) =
      algebraMap S
        (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)) a := sorry

/-- Tag `00QR`: finite-stage evaluation commutes with the completed basic-open comparison
from a subalgebra. -/
@[stacks 00QR "completed subalgebra basic-open localization equivalence"]
theorem completionEquivOfAwayMapBijective_evalₐ
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r : A) (hrq : (r : S) ∉ q)
    (h : Function.Bijective (Localization.awayMap A.val.toRingHom r)) (n : ℕ)
    (x : AdicCompletion
      (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q)))
      (Localization.AtPrime (Ideal.comap A.val.toRingHom q))) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) n
        (completionEquivOfAwayMapBijective A r hrq h x) =
      RingEquiv.MaximalIdeal.quotientPowEquiv
        (localRingEquivOfAwayMapBijective A r hrq h) n
        (AdicCompletion.evalₐ
          (maximalIdeal (Localization.AtPrime (Ideal.comap A.val.toRingHom q))) n x) := sorry

end Subalgebra
