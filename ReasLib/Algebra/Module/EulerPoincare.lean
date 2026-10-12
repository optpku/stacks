/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Basic
public import Mathlib.Algebra.Exact.Basic

/-!
# Euler-Poincaré functions

Euler-Poincaré functions are additive integer invariants on the Grothendieck group of finite
modules. Evaluation on modules exposes their additivity on short exact sequences.
-/

@[expose] public section

universe u v

open CategoryTheory.ModuleCat

namespace Module

/-- An Euler-Poincaré function is an additive map from the finite-module Grothendieck group to
the integers. -/
abbrev EulerPoincareFunction (A : Type u) [CommRing A] :=
  K0.finite.{u, v} A →+ ℤ

namespace EulerPoincareFunction

/-- The value of an Euler-Poincaré function on a finite module is the image of its
Grothendieck class. -/
def eval {A : Type u} [CommRing A] (φ : EulerPoincareFunction A)
    (M : Type v) [AddCommGroup M] [Module A M] [Module.Finite A M] : ℤ :=
  φ (K0.finiteClass A M)

/-- An Euler-Poincaré function is additive on short exact sequences of finite modules. -/
theorem eval_shortExact {A : Type u} [CommRing A]
    {M' M M'' : Type v} [AddCommGroup M'] [AddCommGroup M] [AddCommGroup M'']
    [Module A M'] [Module A M] [Module A M'']
    [Module.Finite A M'] [Module.Finite A M] [Module.Finite A M'']
    (φ : EulerPoincareFunction A) (f : M' →ₗ[A] M) (g : M →ₗ[A] M'')
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    eval φ M = eval φ M' + eval φ M'' := sorry

end EulerPoincareFunction

end Module
