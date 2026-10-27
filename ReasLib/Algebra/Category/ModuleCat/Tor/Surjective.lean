/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Abelian.LeftDerived
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.RingTheory.Ideal.Tensor.MultiplicationKernel

/-!
# Tor objects for surjective commutative ring homomorphisms

Derived extension of scalars describes self-Tor, dimension shifting to the
kernel ideal, and the multiplication-kernel description of first kernel Tor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.ExtendScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Self-Tor along a ring homomorphism, computed by derived extension of scalars. -/
def selfTorObj (f : R →+* S) (n : ℕ) : ModuleCat.{u} S :=
  ((ModuleCat.extendScalars f).leftDerived n).obj
    ((ModuleCat.restrictScalars f).obj (ModuleCat.of S S))

/-- Tor of the kernel ideal along a ring homomorphism, computed by derived scalar extension. -/
def kernelTorObj (f : R →+* S) (n : ℕ) : ModuleCat.{u} S :=
  ((ModuleCat.extendScalars f).leftDerived n).obj
    (ModuleCat.of R (RingHom.ker f))

/-- Second self-Tor of a surjection is first Tor of its kernel ideal. -/
theorem selfTorTwo_isIsomorphic_kernelTorOne (f : R →+* S)
    (hf : Function.Surjective f) :
    IsIsomorphic (selfTorObj f 2) (kernelTorObj f 1) := sorry

/-- First Tor of the kernel of a surjection is the kernel of ideal tensor multiplication. -/
theorem kernelTorOne_isIsomorphic_mulKer (f : R →+* S)
    (hf : Function.Surjective f) :
    IsIsomorphic (kernelTorObj f 1) (Ideal.mulKerModuleCat f hf) := sorry

end ModuleCat.ExtendScalars
