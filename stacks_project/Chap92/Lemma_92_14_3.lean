/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.RingTheory.CotangentComplex.KoszulRegular
import StacksCheckRecall

/-!
# Cotangent complex of a Koszul-regular quotient

Lemma 92.14.3 identifies `L_{B/A}` in `D(B)` with the conormal module `I/I²`
placed in cohomological degree `-1`, whenever `A → B` is surjective with
Koszul-regular kernel.
-/

open CategoryTheory
open CategoryTheory.Limits
open Algebra

universe u

/- Lemma 92.14.3. Let `A → B` be a surjective ring map whose kernel `I` is Koszul.
Then `L_{B/A}` is quasi-isomorphic to `I/I²[1]`. -/
@[stacks 08SK] #check (Algebra.CotangentComplex.isIsomorphic_single_conormal :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      (h : Function.Surjective (algebraMap A B))
      (hI : (RingHom.ker (algebraMap A B)).IsKoszulRegularIdeal),
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} B) (-1 : ℤ)).obj
        (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent)))

#check (Algebra.CotangentComplex.homology_isZero_of_ne_negOne :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      (h : Function.Surjective (algebraMap A B))
      (hI : (RingHom.ker (algebraMap A B)).IsKoszulRegularIdeal)
      {n : ℤ} (hn : n ≠ -1),
    IsZero ((Algebra.cotangentComplex A B).homology n))

#check (Algebra.CotangentComplex.homology_negOne_isIsomorphic :
    ∀ {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
      (h : Function.Surjective (algebraMap A B))
      (hI : (RingHom.ker (algebraMap A B)).IsKoszulRegularIdeal),
    IsIsomorphic
      ((Algebra.cotangentComplex A B).homology (-1))
      (ModuleCat.of B (Extension.ofSurjective (Algebra.ofId A B) h).Cotangent))

#check (Algebra.CotangentComplex.quotient_isIsomorphic_single_conormal :
    ∀ {A : Type u} [CommRing A] (I : Ideal A) (hI : I.IsKoszulRegularIdeal),
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A (A ⧸ I)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⧸ I)) (-1 : ℤ)).obj
        (ModuleCat.of (A ⧸ I) I.Cotangent)))
