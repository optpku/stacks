module

public import Mathlib.Algebra.DualNumber
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.LinearAlgebra.Span.Basic

/-!
# Scaling dual numbers

This module provides the algebra endomorphism that scales the infinitesimal
coordinate of a dual number and the induced morphism of spectra.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped DualNumber

universe u

namespace DualNumber

variable {R : Type u} [CommRing R]

/-- The `R`-algebra endomorphism of `DualNumber R` sending `ε` to `c • ε`. -/
def scaleAlgHom (c : R) : DualNumber R →ₐ[R] DualNumber R :=
  TrivSqZeroExt.map (LinearMap.toSpanSingleton R R c)

/-- The scaling algebra homomorphism sends `ε` to `c • ε`. -/
theorem scaleAlgHom_eps (c : R) : scaleAlgHom c eps = c • eps := sorry

noncomputable section

/-- The scheme self-map induced by scaling the infinitesimal coordinate by `c`. -/
def scale (c : R) :
    Spec (CommRingCat.of (DualNumber R)) ⟶ Spec (CommRingCat.of (DualNumber R)) :=
  Spec.map (CommRingCat.ofHom (scaleAlgHom c).toRingHom)

end

end DualNumber
