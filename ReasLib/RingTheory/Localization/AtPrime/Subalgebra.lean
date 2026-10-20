/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Prime Localizations of Subalgebras

This leaf turns a bijection on a basic-open comparison from a subalgebra into
a bijection on the corresponding prime localizations.  Mathlib supplies the
lower-level saturation criterion; the result here owns the reusable
denominator-clearing specialization for `Subalgebra`.
-/

@[expose] public section

universe u v

namespace Subalgebra

variable {R : Type u} {S : Type v}
variable [CommSemiring R] [CommSemiring S] [Algebra R S]

/-- The canonical algebra action of the base prime localization on the localization of a
subalgebra at the contracted prime.  It depends on the chosen prime and is therefore explicit
rather than a global instance. -/
@[stacks 00QR "subalgebra prime-local algebra"]
noncomputable abbrev atPrimeAlgebra
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) :
    Algebra (Localization.AtPrime (q.under R))
      (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :=
  (Localization.localRingHom (q.under R) (Ideal.comap A.val.toRingHom q)
    (algebraMap R A) (Ideal.under_under (A := R) (B := A) q)).toAlgebra

/-- Tag `00QR`: if the basic-open map from a subalgebra is bijective and its
denominator avoids a prime of the ambient algebra, then the induced map on
the contracted and ambient prime localizations is bijective. -/
@[stacks 00QR "subalgebra basic-open localization"]
theorem localRingHom_bijective_of_awayMap_bijective
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r : A) (hrq : (r : S) ∉ q)
    (hr : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    let p : Ideal A := Ideal.comap A.val.toRingHom q
    Function.Bijective (Localization.localRingHom p q A.val.toRingHom rfl) := by
  let p : Ideal A := Ideal.comap A.val.toRingHom q
  -- This canonical instance is needed only while applying Mathlib's local theorem to `p`.
  letI : p.IsPrime := Ideal.comap_isPrime A.val.toRingHom q
  -- The local comparison is over the contracted prime, so this proof-local instance is canonical.
  letI : q.LiesOver p := ⟨rfl⟩
  have hsat : A.saturation (q.primeCompl ⊓ A.toSubmonoid) (by simp) = ⊤ := by
    rw [← top_le_iff]
    intro x hx
    obtain ⟨b, n, hb⟩ := (Localization.awayMap_surjective_iff).mp hr.2 x
    refine ⟨r.1 ^ n, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · exact q.primeCompl.pow_mem (show r.1 ∈ q.primeCompl from hrq) n
      · exact A.pow_mem r.2 n
    · simpa [smul_eq_mul] using (show r.1 ^ n * x ∈ A from hb.symm ▸ b.2)
  have hbij : Function.Bijective (Localization.localRingHom p q A.val.toRingHom rfl) :=
    @Localization.localRingHom_bijective_of_saturated_inf_eq_top R _ S _ _ q _ A hsat p _ _
  simpa [p] using hbij

/-- Tag `00QR`: a bijective basic-open comparison from a subalgebra induces an equivalence
of the corresponding prime localizations. -/
@[stacks 00QR "subalgebra basic-open localization equivalence"]
noncomputable def localRingEquivOfAwayMapBijective
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r : A) (hrq : (r : S) ∉ q)
    (h : Function.Bijective (Localization.awayMap A.val.toRingHom r)) :
    Localization.AtPrime (Ideal.comap A.val.toRingHom q) ≃+* Localization.AtPrime q :=
  RingEquiv.ofBijective
    (Localization.localRingHom (Ideal.comap A.val.toRingHom q) q A.val.toRingHom rfl)
    (localRingHom_bijective_of_awayMap_bijective A r hrq h)

/-- Tag `00QR`: `localRingEquivOfAwayMapBijective` is the canonical local-ring comparison
on its forward map. -/
@[stacks 00QR "subalgebra basic-open localization equivalence", simp]
theorem localRingEquivOfAwayMapBijective_apply
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r : A) (hrq : (r : S) ∉ q)
    (h : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : Localization.AtPrime (Ideal.comap A.val.toRingHom q)) :
    localRingEquivOfAwayMapBijective A r hrq h x =
      Localization.localRingHom (Ideal.comap A.val.toRingHom q) q A.val.toRingHom rfl x := sorry

/-- The away-bijective local-ring equivalence of a subalgebra commutes with the canonical map
from the base prime localization. -/
@[stacks 00QR "subalgebra basic-open localization equivalence"]
theorem localRingEquivOfAwayMapBijective_commutes
    {q : Ideal S} [q.IsPrime] (A : Subalgebra R S) (r : A) (hrq : (r : S) ∉ q)
    (h : Function.Bijective (Localization.awayMap A.val.toRingHom r))
    (x : Localization.AtPrime (q.under R)) :
    letI : Algebra (Localization.AtPrime (q.under R))
        (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) := atPrimeAlgebra A
    letI : Algebra (Localization.AtPrime (q.under R)) (Localization.AtPrime q) :=
      Localization.AtPrime.algebraOfLiesOver (q.under R) q
    localRingEquivOfAwayMapBijective A r hrq h
        (algebraMap
          (Localization.AtPrime (q.under R))
          (Localization.AtPrime (Ideal.comap A.val.toRingHom q)) x) =
      algebraMap (Localization.AtPrime (q.under R)) (Localization.AtPrime q) x := sorry

end Subalgebra
