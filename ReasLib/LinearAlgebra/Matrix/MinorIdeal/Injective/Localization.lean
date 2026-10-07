module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localized coordinate maps

This leaf records the prime-localization bridge used by the rank-minor
injectivity criterion.

@stack 00MX
-/

universe u

namespace LinearMap.Localization

variable {R : Type u} [CommRing R]
variable {m n : ℕ}

/-- The coordinate matrix of an injective finite free-module map remains
injective after base change to the localization at a prime. -/
@[stacks 00MX "localized coordinate matrix"]
theorem coordinateMap_injective
    {p : Ideal R} [p.IsPrime]
    (φ : (Fin m → R) →ₗ[R] (Fin n → R))
    (hφ : Function.Injective φ) :
    Function.Injective
      ((LinearMap.toMatrix (Pi.basisFun R (Fin m)) (Pi.basisFun R (Fin n)) φ).map
        (algebraMap R (Localization.AtPrime p))).toLin' := sorry

end LinearMap.Localization
