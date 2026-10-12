/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite presentation under ring equivalences

This leaf records the canonical restriction-of-scalars transport of finite
presentation along a ring equivalence.  The module action in the conclusion is
determined by the supplied equivalence and is therefore local rather than a
global instance.

@stack 051X
-/

@[expose] public section

universe u v w

namespace Module.FinitePresentation

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {M : Type w} [AddCommGroup M] [Module S M]

/-- Finite presentation is preserved when a module is viewed over a ring equivalent to its
original scalar ring. -/
@[stacks 051X "finite-presentation transport under ring equivalences"]
theorem compHom_of_ringEquiv
    (e : R ≃+* S) [Module.FinitePresentation S M] :
    letI : Module R M := Module.compHom M e.toRingHom
    Module.FinitePresentation R M := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  letI : Module R M := Module.compHom M e.toRingHom
  letI : IsScalarTower R S M := RestrictScalars.isScalarTower R S M
  letI : Module.FinitePresentation R S :=
    Module.FinitePresentation.of_equiv (Module.compHom.toLinearEquiv e)
  exact Module.FinitePresentation.trans (R := R) (M := M) S

/-- Finite presentation over equivalent scalar rings is equivalent after transporting the
module action along the ring equivalence. -/
@[stacks 051X "finite-presentation equivalence under ring equivalences"]
theorem compHom_iff_of_ringEquiv (e : R ≃+* S) :
    letI : Module R M := Module.compHom M e.toRingHom
    Module.FinitePresentation R M ↔ Module.FinitePresentation S M := by
  letI : Module R M := Module.compHom M e.toRingHom
  constructor
  · intro hM
    letI : Module.FinitePresentation R M := hM
    letI : Algebra S R := e.symm.toRingHom.toAlgebra
    letI : IsScalarTower S R M :=
      IsScalarTower.of_algebraMap_smul fun s m => by
        change e (e.symm s) • m = s • m
        rw [e.apply_symm_apply]
    letI : Module.FinitePresentation S R :=
      Module.FinitePresentation.of_equiv (Module.compHom.toLinearEquiv e.symm)
    exact Module.FinitePresentation.trans (R := S) (M := M) R
  · intro hM
    letI : Module.FinitePresentation S M := hM
    exact compHom_of_ringEquiv e

end Module.FinitePresentation
