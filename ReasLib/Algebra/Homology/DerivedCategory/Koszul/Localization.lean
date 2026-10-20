module

public import ReasLib.Algebra.Homology.DerivedCategory.Koszul.Family
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.RingHom.Flat

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace CategoryTheory.DerivedCategory

/-- A perfect complex with a prime-local Koszul presentation spreads to a principal open while
preserving the regular sequence, flat quotient, and Koszul identification. -/
theorem exists_koszul_localization_away
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.Flat R S] [IsNoetherianRing R]
    [IsNoetherianRing S] (p : Ideal R) (q : Ideal S) [hp : p.IsPrime]
    [hq : q.IsPrime] (hqp : Ideal.comap (algebraMap R S) q = p)
    {r : ℕ} (f : Fin r → Localization.AtPrime q)
    (hf_mem : ∀ i, f i ∈ Ideal.map (algebraMap S (Localization.AtPrime q)) q)
    (hf_reg : RingTheory.Sequence.IsRegular
      (Localization.AtPrime q) (List.ofFn f))
    (hquot_flat : Module.Flat R
      (Localization.AtPrime q ⧸ Ideal.span (Set.range f)))
    (K : DerivedCategory (ModuleCat S)) (hK_perfect : K.IsPerfect)
    (hK_q : IsIsomorphic
      (((ModuleCat.ExtendScalars.exact (algebraMap S (Localization.AtPrime q))
        (RingHom.flat_algebraMap_iff.mpr
          (IsLocalization.flat (Localization.AtPrime q) q.primeCompl))).mapDerivedCategory).obj K)
      (KoszulComplex.derivedFamily f)) :
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
          (KoszulComplex.derivedFamily f') := sorry

end CategoryTheory.DerivedCategory
