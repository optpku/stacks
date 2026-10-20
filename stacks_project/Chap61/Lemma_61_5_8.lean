module

public import ReasLib.Algebra.WLocalHull.ResidueField
import StacksCheckRecall

@[expose] public section

universe u

open Algebra.WLocalHull

/- Lemma 61.5.8 (1): every point of V(IB) is a closed point of Spec(B). -/
@[stacks 097A] #check (Algebra.WLocalHull.zeroLocus_map_subset_closedPoints :
  ∀ {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A) [WLocalSpace (PrimeSpectrum A)],
    PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A) →
    Algebra.IsAlgebraicOnResidueFields A B →
    PrimeSpectrum.zeroLocus (I.map (algebraMap A B) : Set B) ⊆
      closedPoints (PrimeSpectrum B))

/- Lemma 61.5.8 (2): B → C is ind-Zariski, with C := alongClosed B (IB). -/
@[stacks 097A] #check (Algebra.WLocalHull.alongClosed_indZariski :
  ∀ (B : Type u) [CommRing B] (J : Ideal B),
    (algebraMap B (alongClosed B J)).IndZariski)

/- Lemma 61.5.8 (3): B ⧸ IB → C ⧸ IC is an isomorphism. -/
@[stacks 097A] #check (Algebra.WLocalHull.bijective_quotientMap_alongClosed_map :
  ∀ {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A) [WLocalSpace (PrimeSpectrum A)],
    PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A) →
    Algebra.IsAlgebraicOnResidueFields A B →
    Function.Bijective
      (Ideal.quotientMap
        ((I.map (algebraMap A B)).map
          (algebraMap B (alongClosed B (I.map (algebraMap A B)))))
        (algebraMap B (alongClosed B (I.map (algebraMap A B))))
        Ideal.le_comap_map))

/- Lemma 61.5.8 (4): Spec(C) is w-local. -/
@[stacks 097A] #check (Algebra.WLocalHull.wLocalSpace_alongClosed_map :
  ∀ {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A) [WLocalSpace (PrimeSpectrum A)],
    PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A) →
    Algebra.IsAlgebraicOnResidueFields A B →
    WLocalSpace (PrimeSpectrum (alongClosed B (I.map (algebraMap A B)))))

/- Lemma 61.5.8 (5): p : Spec(C) → Spec(A) is w-local. -/
@[stacks 097A] #check (Algebra.WLocalHull.instIsWLocalMap_comap_alongClosed :
  ∀ {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A) [WLocalSpace (PrimeSpectrum A)]
    [Fact (PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A))]
    [Fact (Algebra.IsAlgebraicOnResidueFields A B)],
    IsWLocalMap (PrimeSpectrum.comap (alongClosedComp B I)))

/- Lemma 61.5.8 (6): p⁻¹(X_0) is the set of closed points of Spec(C). -/
@[stacks 097A] #check (Algebra.WLocalHull.comap_preimage_closedPoints_alongClosed :
  ∀ {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]
    (I : Ideal A) [WLocalSpace (PrimeSpectrum A)],
    PrimeSpectrum.zeroLocus (I : Set A) = closedPoints (PrimeSpectrum A) →
    Algebra.IsAlgebraicOnResidueFields A B →
    PrimeSpectrum.comap (alongClosedComp B I) ⁻¹' closedPoints (PrimeSpectrum A) =
      closedPoints (PrimeSpectrum (alongClosed B (I.map (algebraMap A B)))))
