module

public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.FinitePresentation
public import ReasLib.Algebra.Module.FinitePresentation.Relative
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Transitivity and base change for relative finite presentation
-/

universe u v w x

open scoped TensorProduct

-- Local instance justification (instance diamond): select the right tensor-factor algebra only
-- for the source-facing base-change orientation in this leaf.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace Algebra.TensorProduct

variable {R : Type u} {P : Type v} {A : Type w} {R' : Type x}
variable [CommRing R] [CommRing P] [CommRing A] [CommRing R']
variable [Algebra R P] [Algebra R A] [Algebra R R']

/-- The canonical `R'`-algebra map obtained by base changing an `R`-algebra map on the left
tensor factor. -/
@[stacks 065B "base-changed algebra map"]
noncomputable def baseChangeLeftMap (α : P →ₐ[R] A) :
    (P ⊗[R] R') →ₐ[R'] (A ⊗[R] R') :=
  (Algebra.TensorProduct.commRight R R' A).toAlgHom.comp
    ((Algebra.TensorProduct.lTensor R' α).comp
      (Algebra.TensorProduct.commRight R R' P).symm.toAlgHom)

/-- The base-changed algebra map sends a pure tensor to the corresponding pure tensor. -/
@[stacks 065B "base-changed algebra map on pure tensors"]
theorem baseChangeLeftMap_tmul (α : P →ₐ[R] A) (p : P) (r : R') :
    baseChangeLeftMap (R' := R') α (p ⊗ₜ[R] r) = α p ⊗ₜ[R] r := sorry
/- Proof strategy: unfold `baseChangeLeftMap` and simplify the two `commRight` maps and
`Algebra.TensorProduct.lTensor` on the pure tensor `p ⊗ₜ[R] r`. -/

/-- Base change preserves surjectivity of an algebra map. -/
@[stacks 065B "surjectivity of a base-changed algebra map"]
theorem baseChangeLeftMap_surjective (α : P →ₐ[R] A)
    (hα : Function.Surjective α) :
    Function.Surjective (baseChangeLeftMap (R' := R') α) := sorry
/- Proof strategy: use tensor-product induction on the target, choose preimages of the left
factors with `hα`, and rewrite pure tensors with `baseChangeLeftMap_tmul`; preserve sums and
scalar multiples through the `AlgHom` structure. -/

end Algebra.TensorProduct

namespace Module.FinitePresentationRelativeTo

/-- Relative finite presentation is transitive across a finitely presented
intermediate algebra. -/
@[stacks 065C "transitivity of relative finite presentation"]
theorem trans
    {R : Type u} {A : Type v} {B : Type w} {M : Type x}
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [AddCommGroup M] [Module B M] [Algebra.FinitePresentation R A]
    (hM : Module.FinitePresentationRelativeTo A B M) :
    Module.FinitePresentationRelativeTo R B M := sorry
/- Proof strategy: choose a finite polynomial presentation of `A` over `R` from
`Algebra.FinitePresentation R A`, combine it with a witness presentation of `B` over `A`, and
transport the finite-presentation-along condition across the resulting finite polynomial
presentation of `B` over `R` using the presentation-independence API. -/

/-- Relative finite presentation is preserved by extension of scalars along a
finitely presented algebra map. -/
@[stacks 0670 "base change of relative finite presentation"]
theorem baseChange
    {R : Type u} {A : Type v} {A' : Type w} {M : Type x}
    [CommRing R] [CommRing A] [CommRing A']
    [Algebra R A] [Algebra A A'] [Algebra R A'] [IsScalarTower R A A']
    [AddCommGroup M] [Module A M] [Algebra.FinitePresentation A A']
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R A' (A' ⊗[A] M) := sorry
/- Proof strategy: choose a polynomial-presentation witness for `hM`, base change its module
presentation along `A → A'`, and use finite presentation of `A'` over `A` together with
`Module.FinitePresentation.trans` to package a relative presentation over `R`. -/

/-- Changing the base ring preserves relative finite presentation. -/
@[stacks 065B "base-ring change of relative finite presentation"]
theorem baseChangeBaseRing
    {R : Type u} {A : Type v} {M : Type w} {R' : Type x}
    [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [AddCommGroup M] [Module A M]
    (hM : Module.FinitePresentationRelativeTo R A M) :
    Module.FinitePresentationRelativeTo R' (A ⊗[R] R')
      ((A ⊗[R] R') ⊗[A] M) := sorry
/- Proof strategy: base change the polynomial-presentation witness for `hM` from `R` to `R'`;
use `baseChangeLeftMap_surjective` for the new presentation map and the standard tensor-product
finite-presentation instance for the module, then identify the resulting scalar extension with
`(A ⊗[R] R') ⊗[A] M`. -/

end Module.FinitePresentationRelativeTo
