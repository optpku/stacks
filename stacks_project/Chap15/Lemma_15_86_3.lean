/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Pushout
import StacksCheckRecall

/-!
# Lemma 15.86.3

@stack 0FJU
-/

@[expose] public section

open Algebra
open CategoryTheory ComplexShape
open scoped DerivedTensorWithAlgebra NaiveCotangent TensorProduct

universe u

-- Source compatibility note: the pushout carries two canonical algebra structures.  They are
-- selected only in this facade so the explicit map types elaborate without a global diamond.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

section

variable (A A' B : Type u) [CommRing A] [CommRing A'] [CommRing B]
variable [Algebra A A'] [Algebra A B]

/- The canonical pushout comparison is owned at the chain, cochain, and derived-category levels. -/
@[stacks 0FJU "canonical chain-level pushout comparison"]
#check (NaiveCotangent.Pushout.chainMap A A' B :
  Extension.NaiveCotangent.ExtendScalars.source
      ((Generators.self A B : Generators A B B).toExtension) ⟶
    Extension.NaiveCotangent.complex
      ((Generators.self A' (A' ⊗[A] B) :
        Generators A' (A' ⊗[A] B) (A' ⊗[A] B)).toExtension))

@[stacks 0FJU "canonical cochain-level pushout comparison"]
#check (NaiveCotangent.Pushout.cochainMap A A' B :
  ((ModuleCat.extendScalars (algebraMap B (A' ⊗[A] B))).mapHomologicalComplex (up ℤ)).obj
      ((NL{B⁄A}).extend embeddingDownNat) ⟶
    (NL{A' ⊗[A] B⁄A'}).extend embeddingDownNat)

@[stacks 0FJU "canonical underived pushout comparison"]
#check (NaiveCotangent.Pushout.underivedComparison A A' B :
  NaiveCotangent.Pushout.underivedBaseChangeObject A A' B ⟶
    Algebra.naiveCotangentObject A' (A' ⊗[A] B))

@[stacks 0FJU "canonical derived pushout comparison"]
#check (NaiveCotangent.Pushout.derivedComparison A A' B :
  (Algebra.naiveCotangentObject A B ⊗[B]^L[A' ⊗[A] B]) ⟶
    Algebra.naiveCotangentObject A' (A' ⊗[A] B))

/- Lemma 15.86.3 (1) (0FJU): if `B` is flat over `A`, the canonical underived pushout
comparison is an isomorphism. -/
variable [Module.Flat A B]

@[stacks 0FJU "(1), flat underived pushout comparison"]
#check (NaiveCotangent.Pushout.underivedComparison_isIso_of_flat A A' B :
  IsIso (NaiveCotangent.Pushout.underivedComparison A A' B))

/- Lemma 15.86.3 (2) (0FJU): with Tor-amplitude in `[-1, 0]`, the canonical derived pushout
comparison is also an isomorphism. -/
variable (hNL : DerivedCategory.HasTorAmplitudeIn
  (R := B) (Algebra.naiveCotangentObject A B) (-1) 0)

@[stacks 0FJU "(2), flat derived pushout comparison"]
#check (NaiveCotangent.Pushout.derivedComparison_isIso_of_flat_of_hasTorAmplitudeIn
    A A' B hNL :
  IsIso (NaiveCotangent.Pushout.derivedComparison A A' B))

end

end
