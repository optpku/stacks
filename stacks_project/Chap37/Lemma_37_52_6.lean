/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.QuasiFinite.LocalRing
import StacksCheckRecall

universe u v

@[expose] public section

/- Lemma 37.52.6: for a local essentially finite-type map of Noetherian local
rings with finite residue-field extension, an open part of `PrimeSpectrum B`
containing a point away from the closed fibre contains a prime `q` away from
the closed fibre such that `A → B ⧸ q.asIdeal` is a localization of a
finite-type quasi-finite `A`-algebra. -/
@[stacks 05GT]
#check
  (@Algebra.EssFiniteType.exists_prime_mem_open_localization_quasiFinite.{u, v} :
    ∀ {A : Type u} {B : Type v} [CommRing A] [CommRing B]
      [Algebra A B] [IsLocalRing A] [IsLocalRing B]
      [IsLocalHom (algebraMap A B)] [IsNoetherianRing A]
      [Algebra.EssFiniteType A B]
      [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
      (V : TopologicalSpace.Opens (PrimeSpectrum B)),
      (∃ p : PrimeSpectrum B,
        p ∈ V ∧ IsLocalRing.maximalIdeal A ≠
          p.asIdeal.comap (algebraMap A B)) →
        ∃ q : PrimeSpectrum B,
          q ∈ V ∧ IsLocalRing.maximalIdeal A ≠
            q.asIdeal.comap (algebraMap A B) ∧
          ∃ (C : Subalgebra A (B ⧸ q.asIdeal)) (M : Submonoid C),
            Algebra.FiniteType.QuasiFinite A C ∧
              IsLocalization M (B ⧸ q.asIdeal))

end
