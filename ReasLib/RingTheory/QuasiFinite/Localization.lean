/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.RingHom.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Localization.Away.Ideal
public import ReasLib.RingTheory.Localization.Away.Relative
public import ReasLib.RingTheory.QuasiFinite.FiniteType

@[expose] public section

/-!
# Quasi-finiteness at localized primes

This leaf records the primewise invariance of `Algebra.QuasiFiniteAt` under a
target localization when the localized prime contracts to the original one.

The product-localization API for Stacks tag `077H` lives here as a thin
quasi-finiteness layer over the generic ideal and relative-localization owners.

@stack 077H
@stack 0C6H
-/

universe u v w

namespace Algebra.QuasiFiniteAt

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A bijective standard local-ring map `Rₚ → S_q` makes the target localization
quasi-finite over `R`. -/
@[stacks 00QR "quasi-finite local isomorphism"]
theorem of_bijective_localRingHom
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hq : q.LiesOver p)
    (hlocal :
      Function.Bijective (Localization.localRingHom p q (algebraMap R S) hq.over)) :
    Algebra.QuasiFiniteAt R q := by
  -- Local instance justification (proof-local temporary data): the algebra action is induced by
  -- the explicit local-ring map whose bijectivity is assumed in `hlocal`.
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q (algebraMap R S) hq.over).toAlgebra
  have hlocal' :
      Function.Bijective
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) := by
    simpa [RingHom.algebraMap_toAlgebra] using hlocal
  let e : Localization.AtPrime p ≃ₐ[Localization.AtPrime p] Localization.AtPrime q :=
    AlgEquiv.ofBijective (Algebra.ofId _ _) hlocal'
  let eR : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime p := e.symm.restrictScalars R
  exact (Algebra.QuasiFinite.iff_of_algEquiv (R := R) eR).mpr inferInstance

/-- Localizing the target does not change quasi-finiteness at a prime and its contraction. -/
@[stacks 00PL "quasi-finite localization"]
theorem iff_localization_comap (M : Submonoid S) (Q : Ideal (Localization M)) [Q.IsPrime] :
    Algebra.QuasiFiniteAt R (Q.comap (algebraMap S (Localization M))) ↔
      Algebra.QuasiFiniteAt R Q := sorry

section Tower

variable {R A T : Type*} [CommRing R] [CommRing A] [CommRing T]
  [Algebra R A] [Algebra A T] [Algebra R T] [IsScalarTower R A T]

/-- Quasi-finiteness at a prime is unchanged when the base is replaced by a
quasi-finite intermediate algebra. -/
@[stacks 077H "quasi-finite base comparison"]
theorem iff_of_quasiFiniteBase [Algebra.QuasiFinite R A]
    (q : Ideal T) [q.IsPrime] :
    Algebra.QuasiFiniteAt R q ↔ Algebra.QuasiFiniteAt A q := sorry

end Tower

section AwayProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- The canonical away-product comparison for `Algebra.QuasiFiniteAt`.  The
finite-type hypothesis is intentionally absent: this is the reusable Mathlib-level
predicate, while `iff_awayMul_of_finiteType` below is the source-facing bridge. -/
@[stacks 077H "quasi-finite away-product comparison"]
theorem iff_awayMul (f : R) (g : S) (q : Ideal S) [q.IsPrime]
    (hf : f ∉ q.comap (algebraMap R S)) (hg : g ∉ q) :
    -- Local instance justification (proof-local temporary data): primality depends on the
    -- explicit avoidance hypotheses `hf` and `hg`.
    letI : (q.mapAwayMul f g).IsPrime := Ideal.mapAwayMul_isPrime q f g hf hg
    -- Local instance justification (instance diamond): this relative action can compete with
    -- another ambient action on the same localization.
    letI : Algebra (Localization.Away f)
        (Localization.Away ((algebraMap R S f) * g)) :=
      Localization.Away.Relative.mapMulAlgebra (algebraMap R S) f g
    Algebra.QuasiFiniteAt R q ↔
      Algebra.QuasiFiniteAt (Localization.Away f) (q.mapAwayMul f g) := sorry

/-- Lemma 10.122.6: for a finite-type map `R → S`, a prime `q` lying over
`p`, and elements avoiding `p` and `q`, quasi-finiteness at `q` is equivalent
to quasi-finiteness after passing to `R_f → S_(f g)`.  The base prime `p` is
kept in this source-facing bridge; the generic owner above uses the contracted
prime `q.comap (algebraMap R S)`. -/
@[stacks 077H "Lemma 10.122.6 source bridge"]
theorem iff_awayMul_of_finiteType [Algebra.FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p]
    (f : R) (g : S) (hf : f ∉ p) (hg : g ∉ q) :
    -- Local instance justification (proof-local temporary data): primality depends on the
    -- explicit avoidance hypotheses `hf` and `hg`.
    letI : (q.mapAwayMul f g).IsPrime :=
      Ideal.mapAwayMul_isPrime_of_liesOver p q f g hf hg
    -- Local instance justification (instance diamond): this relative action can compete with
    -- another ambient action on the same localization.
    letI : Algebra (Localization.Away f)
        (Localization.Away ((algebraMap R S f) * g)) :=
      Localization.Away.Relative.mapMulAlgebra (algebraMap R S) f g
    Algebra.QuasiFiniteAt R q ↔
      Algebra.QuasiFiniteAt (Localization.Away f) (q.mapAwayMul f g) := sorry

end AwayProduct

/-- Quasi-finiteness at a target prime is preserved after restricting scalars
along a tower of commutative algebras. -/
@[stacks 0C6H "quasi-finite restriction of scalars"]
theorem of_restrictScalars
    {T : Type w} [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    (q : Ideal T) [q.IsPrime] (h : Algebra.QuasiFiniteAt R q) :
    Algebra.QuasiFiniteAt S q := sorry

end Algebra.QuasiFiniteAt

namespace Algebra.FiniteType.QuasiFiniteAt

variable {R : Type u} {S : Type v} {T : Type w}
  [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- Lemma 10.122.10: finite-type quasi-finiteness at a target prime is
preserved after restricting scalars along a tower of commutative algebras. -/
@[stacks 0C6H]
theorem of_restrictScalars (q : Ideal T) [q.IsPrime]
    (h : Algebra.FiniteType.QuasiFiniteAt R T q) :
    Algebra.FiniteType.QuasiFiniteAt S T q := sorry

end Algebra.FiniteType.QuasiFiniteAt

namespace Algebra.QuasiFinite

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- A quasi-finite algebra is quasi-finite at every target prime. -/
@[stacks 00PL "global-to-local quasi-finiteness"]
theorem quasiFiniteAt [Algebra.QuasiFinite R S] (q : Ideal S) [q.IsPrime] :
    Algebra.QuasiFiniteAt R q := sorry

end Algebra.QuasiFinite
