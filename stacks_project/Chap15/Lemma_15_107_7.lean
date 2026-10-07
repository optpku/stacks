module

import StacksCheckRecall
public import ReasLib.RingTheory.LocalRing.Branches.Unibranch

/-!
@stack 0C37
-/

@[expose] public section

open Ideal
open scoped Unibranch

universe u v

/- Lemma 15.107.7 (1), branch part, tag `0C37`: infinitely many minimal primes force infinitely
many branches. -/
@[stacks 0C37 "Lemma 15.107.7 (1), branch part"]
#check fun (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (h : (minimalPrimes A).Infinite) ↦
  (BranchNumber.eq_top_of_infinite_minimalPrimes (A := A) (Ah := Ah) h :
    branchNumber A Ah = ⊤)

/- Lemma 15.107.7 (1), geometric part, tag `0C37`: infinitely many minimal primes force
infinitely many geometric branches. -/
@[stacks 0C37 "Lemma 15.107.7 (1), geometric part"]
#check fun (A : Type u) (Ash : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    (h : (minimalPrimes A).Infinite) ↦
  (GeometricBranchNumber.eq_top_of_infinite_minimalPrimes (A := A) (Ash := Ash) h :
    geometricBranchNumber A Ash = ⊤)

/- Lemma 15.107.7 (2), tag `0C37`: a local ring has one branch exactly when it is unibranch. -/
@[stacks 0C37 "Lemma 15.107.7 (2)"]
#check fun (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah] ↦
  (BranchNumber.eq_one_iff_isUnibranch (A := A) (Ah := Ah) :
    branchNumber A Ah = 1 ↔ IsUnibranch A)

/- Lemma 15.107.7 (3), tag `0C37`: a local ring has one geometric branch exactly when it is
geometrically unibranch. -/
@[stacks 0C37 "Lemma 15.107.7 (3)"]
#check fun (A : Type u) (Ash : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash] ↦
  (GeometricBranchNumber.eq_one_iff_isGeometricallyUnibranch (A := A) (Ash := Ash) :
    geometricBranchNumber A Ash = 1 ↔ IsGeometricallyUnibranch A)

/- Lemma 15.107.7 (4), tag `0C37`: when the minimal-prime set is finite, branches are counted by
the maximal spectrum of the normalization of the reduction. -/
@[stacks 0C37 "Lemma 15.107.7 (4)"]
#check fun (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ah] [Algebra A Ah] [IsHenselizationOf A Ah]
    (h : (minimalPrimes A).Finite) ↦
  (BranchNumber.eq_card_normalization (A := A) (Ah := Ah) h :
    branchNumber A Ah = ENat.card (MaximalSpectrum A′))

/- Lemma 15.107.7 (5), tag `0C37`: when the minimal-prime set is finite, geometric branches are
the maximal points of the normalization weighted by their residue-field embedding types. -/
@[stacks 0C37 "Lemma 15.107.7 (5)"]
#check fun (A : Type u) (Ash : Type v) [CommRing A] [IsLocalRing A]
    [CommRing Ash] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    (h : (minimalPrimes A).Finite) ↦
  (GeometricBranchNumber.eq_card_normalization (A := A) (Ash := Ash) h :
    geometricBranchNumber A Ash =
      ENat.card
        (Σ m : MaximalSpectrum A′, Field.Emb (IsLocalRing.ResidueField A) m.ResidueField))
