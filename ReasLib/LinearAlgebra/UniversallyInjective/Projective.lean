module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import ReasLib.LinearAlgebra.UniversallyInjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Universal injectivity between projective modules

@stack 05GP

This file records the criterion for ordinary injectivity to be stable under every tensor base
change when proper finitely generated ideals have nonzero annihilator.
-/

@[expose] public section

universe u v w

namespace LinearMap.UniversallyInjective

variable {R : Type u} [CommRing R]
variable {N : Type v} [AddCommGroup N] [Module R N] [Module.Projective R N]
variable {M : Type w} [AddCommGroup M] [Module R M] [Module.Projective R M]

/-- Lemma 15.15.3: if every proper finitely generated ideal of `R` has nonzero annihilator,
then an `R`-linear map between projective modules is universally injective exactly when it is
injective. -/
@[stacks 05GP "Lemma 15.15.3"]
theorem iff_injective_of_projective_of_annihilator
    (hR : ∀ {I : Ideal R}, I.FG → I ≠ ⊤ → I.annihilator ≠ (⊥ : Ideal R))
    (f : N →ₗ[R] M) :
    LinearMap.UniversallyInjective.{u, v, w, u} f ↔ Function.Injective f := sorry
-- Proof strategy: the forward implication specializes tensor injectivity to `Q = R` and uses
-- `TensorProduct.rid`.  Conversely split the projective source off a free module, stabilize `f`
-- to an injective map with free source, and reduce each finite-support piece to a finite free
-- source.  Induct on its rank; the rank-one step uses `hR` on the finitely generated coordinate
-- ideal to construct a retraction, after which split maps remain injective under every tensor.

end LinearMap.UniversallyInjective
