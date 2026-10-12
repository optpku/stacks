/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.PseudoCoherent
import StacksCheckRecall

/-!
# Lemma 15.65.12

Lemma 15.65.12 (Stacks `0650`) is a source-facing specialization of the explicit-ring-hom
extension API.  The canonical owner is independent of tensor notation; the full-type checks below
fix the source's `A → B`/derived-tensor spelling without introducing duplicate aliases.

@stack 0650
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v w

/- Lemma 15.65.12 (1): derived extension of scalars preserves `m`-pseudo-coherence. -/
@[stacks 0650 "Lemma 15.65.12 (1)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (K : DerivedCategory (ModuleCat.{w, u} A)) (m : ℤ) (hK : K.IsMPseudoCoherent m) ↦
  (DerivedCategory.IsMPseudoCoherent.extension hK (algebraMap A B) :
    (K ⊗[A]^L[B]).IsMPseudoCoherent m)

/- Lemma 15.65.12 (2): derived extension of scalars preserves pseudo-coherence. -/
@[stacks 0650 "Lemma 15.65.12 (2)"]
#check fun {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (K : DerivedCategory (ModuleCat.{w, u} A)) (hK : K.IsPseudoCoherent) ↦
  (DerivedCategory.IsPseudoCoherent.extension hK (algebraMap A B) :
    (K ⊗[A]^L[B]).IsPseudoCoherent)

#check @DerivedCategory.IsMPseudoCoherent.extension
#check @DerivedCategory.IsPseudoCoherent.extension

end
