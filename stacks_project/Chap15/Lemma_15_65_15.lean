/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent.FaithfullyFlat

import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/-!
@stack 068R

Lemma 15.65.15 is recalled from the canonical faithfully flat descent API for pseudo-coherence.
The explicit ring-map interface is the project formalization of the source's tensor base change.
-/

/- Lemma 15.65.15 (1) (068R): `m`-pseudo-coherence descends along faithfully flat derived
extension of scalars. -/
@[stacks 068R "Lemma 15.65.15 (1)"]
#check fun {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    {K : DerivedCategory (ModuleCat.{w, u} R)} {m : ℤ}
    (hK : ((ModuleCat.derivedExtensionOfScalars.{u, v, w} f
        (hasLeftDerived := ModuleCat.DerivedExtension.Flat.hasLeftDerivedFunctor f hf.flat)).obj K).IsMPseudoCoherent m) ↦
  (CategoryTheory.DerivedCategory.IsMPseudoCoherent.of_faithfullyFlat f hf hK :
    K.IsMPseudoCoherent m)

/- Lemma 15.65.15 (2) (068R): pseudo-coherence descends along faithfully flat derived extension
of scalars. -/
@[stacks 068R "Lemma 15.65.15 (2)"]
#check fun {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    {K : DerivedCategory (ModuleCat.{w, u} R)}
    (hK : ((ModuleCat.derivedExtensionOfScalars.{u, v, w} f
        (hasLeftDerived := ModuleCat.DerivedExtension.Flat.hasLeftDerivedFunctor f hf.flat)).obj K).IsPseudoCoherent) ↦
  (CategoryTheory.DerivedCategory.IsPseudoCoherent.of_faithfullyFlat f hf hK :
    K.IsPseudoCoherent)

/- The reusable owners also expose the corresponding two-way faithfully flat criteria. -/
#check @CategoryTheory.DerivedCategory.IsMPseudoCoherent.extension_iff_of_faithfullyFlat
#check @CategoryTheory.DerivedCategory.IsPseudoCoherent.extension_iff_of_faithfullyFlat
