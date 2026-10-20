module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Flatness.MittagLeffler.Properties

@[expose] public section

/-!
# Tensor-Product Characterization of Mittag-Leffler Modules

This leaf owns the characterization of Mittag-Leffler modules by injectivity
of tensor products against arbitrary products of modules.

@stack 059M
@stack 05CN
@stack 05CT
-/

open scoped TensorProduct

universe u v w x

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Proposition 10.89.5, tag `059M`: a module is Mittag-Leffler exactly when tensoring it with
an arbitrary product injects into the product of the corresponding tensor products. -/
@[stacks 059M]
theorem iff_piRightHom_injective :
    Module.MittagLeffler R M ↔
      ∀ (A : Type w) (Q : A → Type x) [∀ a, AddCommGroup (Q a)] [∀ a, Module R (Q a)],
        Function.Injective (TensorProduct.piRightHom R R M Q) := sorry

/-- Lemma 10.88.9, tag `05CN`: the tensor product of two Mittag-Leffler
modules is Mittag-Leffler. -/
@[stacks 05CN]
theorem tensorProduct {N : Type w} [AddCommGroup N] [Module R N]
    (hM : Module.MittagLeffler R M) (hN : Module.MittagLeffler R N) :
    Module.MittagLeffler R (M ⊗[R] N) := sorry

end Module.MittagLeffler

namespace Module.MittagLeffler.RestrictScalars

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
variable {M : Type w} [AddCommGroup M] [Module S M] [Module R M]
variable [IsScalarTower R S M]

/-- Lemma 10.89.11: if `S` is Mittag-Leffler over `R`, while `M` is flat and
Mittag-Leffler over `S`, then `M` is Mittag-Leffler over `R`. -/
@[stacks 05CT]
theorem of_flat [MittagLeffler R S] [Module.Flat S M] [MittagLeffler S M] :
    MittagLeffler R M := sorry

end Module.MittagLeffler.RestrictScalars
