/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.Koszul.Localization
import StacksCheckRecall

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

/- Lemma 57.16.2 -/
@[stacks 0G0P]
#check (CategoryTheory.DerivedCategory.exists_koszul_localization_away :
    ∀ {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
      [Algebra.FiniteType R S] [Module.Flat R S] [IsNoetherianRing R]
      [IsNoetherianRing S],
      (p : Ideal R) → (q : Ideal S) → [p.IsPrime] → [q.IsPrime] →
      Ideal.comap (algebraMap R S) q = p →
      ∀ {r : ℕ},
        (f : Fin r → Localization.AtPrime q) →
        (∀ i, f i ∈ Ideal.map (algebraMap S (Localization.AtPrime q)) q) →
        RingTheory.Sequence.IsRegular
          (Localization.AtPrime q) (List.ofFn f) →
        Module.Flat R (Localization.AtPrime q ⧸ Ideal.span (Set.range f)) →
        (K : DerivedCategory (ModuleCat S)) → K.IsPerfect →
        IsIsomorphic
          (((ModuleCat.ExtendScalars.exact (algebraMap S (Localization.AtPrime q))
            (RingHom.flat_algebraMap_iff.mpr
              (IsLocalization.flat (Localization.AtPrime q) q.primeCompl))).mapDerivedCategory).obj K)
          (KoszulComplex.derivedFamily f) →
        ∃ g : S, g ∉ q ∧
          ∃ (f' : Fin r → Localization.Away g)
            (φ : Localization.Away g →ₐ[S] Localization.AtPrime q),
            (∀ i, φ (f' i) = f i) ∧
            RingTheory.Sequence.IsRegular (Localization.Away g) (List.ofFn f') ∧
            Module.Flat R (Localization.Away g ⧸ Ideal.span (Set.range f')) ∧
            IsIsomorphic
              (((ModuleCat.ExtendScalars.exact (algebraMap S (Localization.Away g))
                (RingHom.flat_algebraMap_iff.mpr
                  (IsLocalization.flat (Localization.Away g) (Submonoid.powers g)))).mapDerivedCategory).obj K)
              (KoszulComplex.derivedFamily f'))
