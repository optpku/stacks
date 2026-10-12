/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.Depth.LinearMap

/-!
# Serre conditions for linear-map modules

This leaf transports the first two Serre conditions from a finite codomain to the module of
linear maps out of a finite module.

@stack 0AV6
-/

@[expose] public section

universe u v w

namespace LinearMap

section Serre

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Lemma 15.23.11 (1): Serre's condition `(S₁)` passes from a finite codomain to the
corresponding linear-map module. -/
@[stacks 0AV6 "Lemma 15.23.11 (1)"]
instance instSerreConditionSOneOfCodomain
    [IsNoetherianRing R] [Module.Finite R M] [Module.SerreConditionS R N 1] :
    Module.SerreConditionS R (M →ₗ[R] N) 1 := sorry

/-- Lemma 15.23.11 (2): Serre's condition `(S₂)` passes from a finite codomain to the
corresponding linear-map module. -/
@[stacks 0AV6 "Lemma 15.23.11 (2)"]
instance instSerreConditionSTwoOfCodomain
    [IsNoetherianRing R] [Module.Finite R M] [Module.SerreConditionS R N 2] :
    Module.SerreConditionS R (M →ₗ[R] N) 2 := sorry

end Serre

section Domain

variable {R : Type u} [CommRing R] [IsDomain R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Lemma 15.23.11 (3): linear maps into a finite torsion-free `(S₂)` module form a
torsion-free `(S₂)` module. -/
@[stacks 0AV6 "Lemma 15.23.11 (3)"]
theorem isTorsionFree_and_serreConditionSTwo_of_codomain
    [IsNoetherianRing R] [Module.Finite R M]
    [Module.IsTorsionFree R N] [Module.SerreConditionS R N 2] :
    Module.IsTorsionFree R (M →ₗ[R] N) ∧
      Module.SerreConditionS R (M →ₗ[R] N) 2 := sorry

end Domain

end LinearMap
