/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.Algebra.AlgHom.Factorisation.Killing
public import ReasLib.RingTheory.RingHom.IndSmooth.Basic

/-!
# Killing ideals across square-zero thickenings

This leaf isolates the smooth ideal-killing step for ind-smooth targets
modulo a square-zero ideal.
-/

@[expose] public section

universe u v w

namespace AlgHom.Factorisation.Smooth.Killing

variable {R : Type u} {Λ : Type w}
variable [CommRing R] [CommRing Λ] [Algebra R Λ]

/-- Lemma 16.5.2 (tag 07CL): a finitely generated ideal in `I B` that is killed by a map from a
smooth algebra can be killed after factoring through another smooth algebra. -/
@[stacks 07CL]
theorem nonempty_of_squareZero
    {B : Type v} [CommRing B] [Algebra R B]
    (I : Ideal R) [Module.Flat R Λ] [Algebra.Smooth R B] (hI : I ^ 2 = ⊥)
    (hquot :
      (algebraMap (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))).IndSmooth)
    (φ : B →ₐ[R] Λ) (J : Ideal B)
    (hJ : J ≤ I.map (algebraMap R B)) (hJfg : J.FG)
    (hφJ : J ≤ RingHom.ker φ.toRingHom) :
    Nonempty (AlgHom.Factorisation.Smooth.Killing φ J) := sorry

end AlgHom.Factorisation.Smooth.Killing
