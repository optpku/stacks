/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex.BaseChange.Homology
import StacksCheckRecall

/-!
# Lemma 15.86.2

@stack 0FUZ
-/

@[expose] public section

open Algebra
open CategoryTheory
open scoped TensorProduct

universe u

-- Source compatibility note: both canonical tensor-factor algebra structures are required by the
-- pushout map types; they remain local to avoid installing competing global instances.
attribute [local instance] Algebra.TensorProduct.leftAlgebra Algebra.TensorProduct.rightAlgebra

/- Lemma 15.86.2 (1) (0FUZ): for every chosen presentation, the canonical base-change chain
map is an isomorphism on `H⁰` and surjective on `H⁻¹`. -/
@[stacks 0FUZ "(1), presentation-level naive cotangent base change"]
#check fun {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] {ι σ : Type u} (P : Presentation R S ι σ) =>
  (Presentation.naiveCotangentBaseChangeMap (R' := R') P :
    Extension.NaiveCotangent.complex P.toExtension.baseChange ⟶
      Extension.NaiveCotangent.complex
        (Generators.baseChange R' P.toGenerators).toExtension)

@[stacks 0FUZ "(1), presentation-level H1 comparison"]
#check fun {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] {ι σ : Type u} (P : Presentation R S ι σ) =>
  (Presentation.naiveCotangentBaseChangeH1Comparison (R' := R') P :
    LinearMap.ker (LinearMap.baseChange (R' ⊗[R] S) P.toExtension.cotangentComplex) →ₗ[R' ⊗[R] S]
      (P.baseChange R').toExtension.H1Cotangent)

@[stacks 0FUZ "(1), presentation-level H1 surjectivity"]
#check fun {R S R' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [Algebra R S] [Algebra R R'] {ι σ : Type u} (P : Presentation R S ι σ) =>
  (Presentation.naiveCotangentBaseChangeH1Comparison_surjective (R' := R') P :
    Function.Surjective (Presentation.naiveCotangentBaseChangeH1Comparison (R' := R') P))

/- Lemma 15.86.2 (2) (0FUZ): the comparison from the tensor product of `NL{S⁄R}` is
bijective in degree zero and surjective in degree minus one. A presentation computes the
degree-minus-one source as the kernel of the tensorized differential. -/

section

variable (R S R' : Type u) [CommRing R] [CommRing S] [CommRing R']
variable [Algebra R S] [Algebra R R']

@[stacks 0FUZ "(2), H0 base-change isomorphism"]
#check (H1Cotangent.baseChangeDegreeZeroComparison_bijective R S R' :
  Function.Bijective (H1Cotangent.baseChangeDegreeZeroComparison
    (R := R) (R' := R') (S := S)))

@[stacks 0FUZ "(2), H1 of the tensor complex, via a presentation"]
#check fun {ι σ : Type u} (P : Presentation R S ι σ) =>
  (Presentation.naiveCotangentBaseChangeH1Comparison (R' := R') P :
    LinearMap.ker (LinearMap.baseChange (R' ⊗[R] S) P.toExtension.cotangentComplex) →ₗ[R' ⊗[R] S]
      (P.baseChange R').toExtension.H1Cotangent)

@[stacks 0FUZ "(2), H1 of the tensor complex is surjective"]
#check fun {ι σ : Type u} (P : Presentation R S ι σ) =>
  (Presentation.naiveCotangentBaseChangeH1Comparison_surjective (R' := R') P :
    Function.Surjective (Presentation.naiveCotangentBaseChangeH1Comparison (R' := R') P))

end

end
