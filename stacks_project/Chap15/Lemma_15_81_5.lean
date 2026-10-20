module

public import ReasLib.Algebra.Module.FinitePresentation.Relative.BaseChange
import StacksCheckRecall

/-!
# Lemma 15.81.5: relative finite presentation after changing the base ring

@stack 065B

The source finite-type hypothesis is already encoded by
`Module.FinitePresentationRelativeTo`: a witness includes a surjective finite-variable
polynomial presentation of the ambient algebra.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

-- Local instance justification (instance diamond): match the shared owner's right tensor-factor
-- algebra when spelling its concrete base-changed `AlgHom` type.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/- Lemma 15.81.5 (Stacks `065B`): if an `A`-module `M` is finitely presented relative to `R`,
then `(A ⊗[R] R') ⊗[A] M` is finitely presented relative to `R'`. -/
@[stacks 065B "Lemma 15.81.5"]
#check fun {R : Type u} {A : Type v} {M : Type w} {R' : Type x}
    [CommRing R] [CommRing A] [CommRing R']
    [Algebra R A] [Algebra R R'] [AddCommGroup M] [Module A M]
    (hM : Module.FinitePresentationRelativeTo R A M) ↦
  (Module.FinitePresentationRelativeTo.baseChangeBaseRing (R' := R') hM :
    Module.FinitePresentationRelativeTo R' (A ⊗[R] R')
      ((A ⊗[R] R') ⊗[A] M))

/- The shared owner also exposes the concrete base-changed algebra map used by later
presentationwise arguments. -/
@[stacks 065B "base-changed presentation map"]
#check fun {R : Type u} {P : Type v} {A : Type w} {R' : Type x}
    [CommRing R] [CommRing P] [CommRing A] [CommRing R']
    [Algebra R P] [Algebra R A] [Algebra R R'] (α : P →ₐ[R] A) ↦
  (Algebra.TensorProduct.baseChangeLeftMap (R' := R') α :
    (P ⊗[R] R') →ₐ[R'] (A ⊗[R] R'))

@[stacks 065B "surjectivity of the base-changed presentation map"]
#check fun {R : Type u} {P : Type v} {A : Type w} {R' : Type x}
    [CommRing R] [CommRing P] [CommRing A] [CommRing R']
    [Algebra R P] [Algebra R A] [Algebra R R']
    (α : P →ₐ[R] A) (hα : Function.Surjective α) ↦
  (Algebra.TensorProduct.baseChangeLeftMap_surjective (R' := R') α hα :
    Function.Surjective (Algebra.TensorProduct.baseChangeLeftMap (R' := R') α))
