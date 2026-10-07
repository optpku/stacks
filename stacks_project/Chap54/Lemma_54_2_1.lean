module

public import ReasLib.FieldTheory.PurelyInseparable.Trace
import StacksCheckRecall

@[expose] public section

open Polynomial

universe u

/- Lemma 54.2.1: for an `R`-algebra homomorphism
`φ : R[x]/(x ^ p - a) →ₐ[R] R[y]/(y ^ p - b)`, the positive-characteristic trace maps
on relative Kähler differentials satisfy `Trₓ = Trᵧ ∘ dφ`. -/
@[stacks 0ADZ] #check (PurelyInseparableTrace.pPowerTrace_natural :
  ∀ (p : ℕ) (hp : p.Prime) (R : Type u) [CommRing R] [Algebra (ZMod p) R]
    (a b : R) (φ : AdjoinRoot (X ^ p - C a) →ₐ[R] AdjoinRoot (X ^ p - C b)),
    PurelyInseparableTrace.trace p hp R a =
      (PurelyInseparableTrace.trace p hp R b).comp
        (PurelyInseparableTrace.mapOfAlgHom φ))
