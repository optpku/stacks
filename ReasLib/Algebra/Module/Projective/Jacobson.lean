/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.OrzechProperty
public import ReasLib.LinearAlgebra.QuotientByIdeal.QuotientRing
public import ReasLib.RingTheory.Ideal.Nakayama.Basic
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite projective modules modulo a Jacobson-radical ideal

@stack 0BC6

An isomorphism between finite projective modules can be detected and lifted after reduction
modulo an ideal contained in the Jacobson radical.
-/

universe u v w

variable {R : Type u} [CommRing R]
variable {P : Type v} [AddCommGroup P] [Module R P]
variable {P' : Type w} [AddCommGroup P'] [Module R P']

open scoped Pointwise

/-- A map from a finite module to a finite projective module is bijective when its reduction
modulo a Jacobson-radical ideal is bijective. -/
theorem bijective_of_bijective_mod_jacobson_of_finite_projective_target
    [Module.Finite R P] [Module.Finite R P'] [Module.Projective R P']
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (f : P →ₗ[R] P')
    (hf : Function.Bijective (f.quotientMapByIdeal I)) :
    Function.Bijective f := sorry

/-- Lemma 15.3.5 (1): a map between finite projective modules is an isomorphism when its
reduction modulo a Jacobson-radical ideal is an isomorphism. -/
@[stacks 0BC6 "(1)"]
theorem bijective_of_bijective_mod_jacobson_of_finite_projective
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R P'] [Module.Projective R P']
    (I : Ideal R) (hI : I ≤ Ring.jacobson R) (f : P →ₗ[R] P')
    (hf : Function.Bijective (f.quotientMapByIdeal I)) :
    Function.Bijective f := sorry

/-- Lemma 15.3.5 (2): an equivalence between the reductions of two finite projective modules
modulo a Jacobson-radical ideal lifts to an equivalence of the original modules. -/
@[stacks 0BC6 "(2)"]
theorem exists_lift_of_quotient_equiv_of_finite_projective
    [Module.Finite R P] [Module.Projective R P]
    [Module.Finite R P'] [Module.Projective R P']
    (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (e : (P ⧸ I • (⊤ : Submodule R P)) ≃ₗ[R ⧸ I]
      (P' ⧸ I • (⊤ : Submodule R P'))) :
    ∃ f : P ≃ₗ[R] P',
      LinearMap.IdealQuotient.map (f : P →ₗ[R] P') I = e.toLinearMap := sorry
