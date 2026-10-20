/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict

@[expose] public section

/-!
# Restriction of scalars and submodule quotients

Restriction of scalars commutes with quotienting by a submodule. This file packages the comparison
at the `ModuleCat` level, so downstream constructions do not need local scalar instances or manual
instance-dictionary transports.
-/

universe u v w

open CategoryTheory

namespace ModuleCat.RestrictScalars

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- The quotient relations defined before and after restriction along `f` agree on the common
underlying carrier. -/
theorem quotientRel_iff (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) (x y : M) :
    Submodule.quotientRel (submodule f M P) x y ↔
      Submodule.quotientRel P x y := Iff.rfl

/-- The carrier equivalence between quotienting before and after restriction of scalars. -/
@[stacks 07VC "restriction of scalars quotient carrier"]
def quotientCarrierEquiv (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) :
    (((ModuleCat.restrictScalars f).obj M) ⧸ submodule f M P) ≃
      ((ModuleCat.restrictScalars f).obj (ModuleCat.of S (M ⧸ P)) : Type w) :=
  Equiv.refl _

/-- The quotient carrier equivalence preserves addition. -/
theorem quotientCarrierEquiv_add (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M)
    (x y : ((ModuleCat.restrictScalars f).obj M) ⧸ submodule f M P) :
    quotientCarrierEquiv f M P (x + y) =
      quotientCarrierEquiv f M P x + quotientCarrierEquiv f M P y := rfl

/-- The quotient carrier equivalence preserves restricted scalar multiplication. -/
theorem quotientCarrierEquiv_smul (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) (r : R)
    (x : ((ModuleCat.restrictScalars f).obj M) ⧸ submodule f M P) :
    quotientCarrierEquiv f M P (r • x) =
      r • quotientCarrierEquiv f M P x := rfl

/-- Restriction along an arbitrary ring homomorphism commutes canonically with quotienting by a
submodule. -/
@[stacks 07VC "restriction of scalars commutes with quotients"]
def quotientEquiv (f : R →+* S) (M : ModuleCat.{w} S) (P : Submodule S M) :
    (((ModuleCat.restrictScalars f).obj M) ⧸ submodule f M P) ≃ₗ[R]
      ((ModuleCat.restrictScalars f).obj
        (ModuleCat.of S (M ⧸ P)) : Type w) :=
  { __ := quotientCarrierEquiv f M P
    map_add' := quotientCarrierEquiv_add f M P
    map_smul' := quotientCarrierEquiv_smul f M P }

/-- The bundled quotient comparison sends a representative to the same representative. -/
@[simp]
theorem quotientEquiv_mk (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) (x : (ModuleCat.restrictScalars f).obj M) :
    quotientEquiv f M P (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x : M ⧸ P) := rfl

/-- The inverse bundled quotient comparison sends a representative to the same representative. -/
@[simp]
theorem quotientEquiv_symm_mk (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) (x : (ModuleCat.restrictScalars f).obj M) :
    (quotientEquiv f M P).symm (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk x :
        ((ModuleCat.restrictScalars f).obj M) ⧸ submodule f M P) := rfl

/-- Categorical form of the bundled quotient comparison. -/
@[stacks 07VC "restriction of scalars commutes with quotients"]
noncomputable def quotientIso (f : R →+* S) (M : ModuleCat.{w} S)
    (P : Submodule S M) :
    ModuleCat.of R
        (((ModuleCat.restrictScalars f).obj M) ⧸ submodule f M P) ≅
      (ModuleCat.restrictScalars f).obj
        (ModuleCat.of S (M ⧸ P)) :=
  (quotientEquiv f M P).toModuleIso

end ModuleCat.RestrictScalars
