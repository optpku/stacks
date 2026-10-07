module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing

/-!
# Finite and projective modules modulo a base ideal

The quotient `M / I M` is the scalar extension `(R / I) ⊗[R] M`.  This file registers the
resulting canonical finite and projective instances over `R / I`.
-/

@[expose] public section

universe u v

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Quotienting a finite module by `I M` gives a finite module over `R / I`. -/
@[stacks 00DV "finite modules modulo a base ideal"]
instance instFiniteQuotientByIdeal (I : Ideal R) [Module.Finite R M] :
    Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  Module.Finite.equiv (Ideal.Quotient.tensorModuleEquiv I M)

/-- Quotienting a projective module by `I M` gives a projective module over `R / I`. -/
@[stacks 00DV "projective modules modulo a base ideal"]
instance instProjectiveQuotientByIdeal (I : Ideal R) [Module.Projective R M] :
    Module.Projective (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M)) :=
  Module.Projective.of_equiv' (Ideal.Quotient.tensorModuleEquiv I M)

end Module
