/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import ReasLib.Algebra.Module.Torsion.Flatness
import StacksCheckRecall

/-!
# Lemma 15.22.11

@stack 0AUW
-/

universe u v

/- Lemma 15.22.11 (1): over a Dedekind domain, an `A`-module is flat exactly when it is
torsion-free. -/
@[stacks 0AUW "Dedekind flatness and torsion-freeness"]
#check fun {A : Type u} [CommRing A] [IsDedekindDomain A]
    {M : Type v} [AddCommGroup M] [Module A M] ↦
  (Module.Flat.iff_isTorsionFree_of_isDedekindDomain (R := A) (M := M) :
    Module.Flat A M ↔ Module.IsTorsionFree A M)

/- Lemma 15.22.11 (2): a finite torsion-free module over a Dedekind domain is finite locally
free. -/
@[stacks 0AUW "finite torsion-free modules are finite locally free"]
#check fun {A : Type u} [CommRing A] [IsDedekindDomain A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] ↦
  (Module.FiniteLocallyFree.of_finite_of_isTorsionFree_of_isDedekindDomain
    (R := A) (M := M) : Module.FiniteLocallyFree A M)

/- Lemma 15.22.11 (3): a finite torsion-free module over a principal ideal domain is free. -/
@[stacks 0AUW "PID finite torsion-free modules are free"]
#check fun {A : Type u} [CommRing A] [IsDomain A] [IsPrincipalIdealRing A]
    {M : Type v} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.IsTorsionFree A M] ↦
  (inferInstance : Module.Free A M)

#check @Module.free_of_finite_type_torsion_free'
