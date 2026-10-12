/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.DividedPowers.Tate
public import ReasLib.RingTheory.RingHom.PseudoCoherent

/-!
# Pseudo-coherent Tate resolutions

This leaf isolates the finiteness refinement for pseudo-coherent ring maps from the foundational
Tate-resolution owner.
-/

@[expose] public section

universe u v w

namespace TateResolution

variable {R : Type u} {S : Type w} [CommRing R] [CommRing S] [Algebra R S]
variable {J : Type v}

/-- A finite polynomial presentation of a pseudo-coherent ring map admits a Tate resolution with
finitely many positive generators in every degree.  The base, target, and finite presentation
index type may live in separate universes. -/
@[stacks 0BZ9 "fixed presentation"]
theorem exists_finite_of_isPseudoCoherent
    [(algebraMap R S).IsPseudoCoherentRingMap] [Finite J]
    (pi0 : MvPolynomial J R →ₐ[R] S) (hpi0 : Function.Surjective pi0) :
    ∃ A : TateResolution.{u, v, w} pi0, A.HasFinitePositiveGenerators := sorry

/-- A pseudo-coherent ring map admits a finite polynomial presentation and a Tate resolution with
finitely many generators in every positive degree. -/
@[stacks 0BZ9 "finite presentation"]
theorem exists_finitePresentation_of_isPseudoCoherent
    [(algebraMap R S).IsPseudoCoherentRingMap] :
    ∃ (n : ℕ) (pi0 : MvPolynomial (Fin n) R →ₐ[R] S),
      Function.Surjective pi0 ∧
        ∃ A : TateResolution.{u, 0, w} pi0, A.HasFinitePositiveGenerators := sorry

end TateResolution
