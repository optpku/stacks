/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent.FaithfullyFlat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Perfectness and faithfully flat extension

@stack 068T

The ring homomorphism is explicit so downstream statements do not need an ambient `Algebra`
instance.  The derived extension object is the canonical scalar-change carrier; only the descent
propositions are deferred.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe uR uS v

namespace CategoryTheory.DerivedCategory.IsPerfect

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Lemma 15.75.13 (Stacks `068T`): perfectness descends along a faithfully flat ring homomorphism.
-/
@[stacks 068T "faithfully flat descent of perfect derived objects"]
theorem of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    {K : DerivedCategory (ModuleCat.{v, uR} R)}
    (hK : ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} f
        (hasLeftDerived := ModuleCat.DerivedExtension.Flat.hasLeftDerivedFunctor f hf.flat)).obj K).IsPerfect) :
    K.IsPerfect := sorry

/-- Lemma 15.75.13 (Stacks `068T`): perfectness is invariant under faithfully flat derived
extension of scalars. -/
@[stacks 068T "perfectness under faithfully flat derived extension"]
theorem extension_iff_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{v, uR} R)) :
    ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} f
        (hasLeftDerived := ModuleCat.DerivedExtension.Flat.hasLeftDerivedFunctor f hf.flat)).obj K).IsPerfect ↔ K.IsPerfect := sorry

end CategoryTheory.DerivedCategory.IsPerfect
