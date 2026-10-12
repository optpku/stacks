/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Faithfully flat descent of pseudo-coherence

@stack 068R

This file states faithfully flat descent directly for an explicit ring homomorphism and the
canonical derived extension-of-scalars functor.  No ambient `Algebra` instance or chosen complex
model appears in the public interface.  The commutative-ring assumption is the canonical module
category model for the derived tensor in the source statement.
-/

open CategoryTheory

noncomputable section

universe uR uS v

namespace CategoryTheory.DerivedCategory.IsMPseudoCoherent

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Lemma 15.65.15 (1) (068R): `m`-pseudo-coherence descends along a faithfully flat ring
homomorphism. -/
@[stacks 068R "faithfully flat descent of m-pseudo-coherence"]
theorem of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    {K : DerivedCategory (ModuleCat.{v, uR} R)} {m : ℤ}
    (hK : ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} f).obj K).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry
-- Proof strategy: descend homology vanishing and finite presentation along `hf`, then induct on
-- the top nonzero homology degree using a finite free approximation and its distinguished cone.

/-- Tag 068R: `m`-pseudo-coherence is invariant under faithfully flat derived extension. -/
@[stacks 068R "m-pseudo-coherence under faithfully flat extension"]
theorem extension_iff_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{v, uR} R)) (m : ℤ) :
    ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} f).obj K).IsMPseudoCoherent m ↔
      K.IsMPseudoCoherent m := sorry
-- Proof strategy: combine `of_faithfullyFlat` with `IsMPseudoCoherent.extension`.

end CategoryTheory.DerivedCategory.IsMPseudoCoherent

namespace CategoryTheory.DerivedCategory.IsPseudoCoherent

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S]

/-- Lemma 15.65.15 (2) (068R): pseudo-coherence descends along a faithfully flat ring
homomorphism. -/
@[stacks 068R "faithfully flat descent of pseudo-coherence"]
theorem of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    {K : DerivedCategory (ModuleCat.{v, uR} R)}
    (hK : ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} f).obj K).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry
-- Proof strategy: apply the faithfully flat `m`-pseudo-coherent descent theorem in every degree
-- and use the all-degree characterization of pseudo-coherence.

/-- Tag 068R: pseudo-coherence is invariant under faithfully flat derived extension. -/
@[stacks 068R "pseudo-coherence under faithfully flat extension"]
theorem extension_iff_of_faithfullyFlat (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : DerivedCategory (ModuleCat.{v, uR} R)) :
    ((ModuleCat.derivedExtensionOfScalars.{uR, uS, v} f).obj K).IsPseudoCoherent ↔
      K.IsPseudoCoherent := sorry
-- Proof strategy: combine `of_faithfullyFlat` with `IsPseudoCoherent.extension`.

end CategoryTheory.DerivedCategory.IsPseudoCoherent
