/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Residue images of algebras

This module identifies the image of a ring map to a field with the quotient by
the kernel of the map and records its canonical scalar structure.
-/

@[expose] public section

universe u v

namespace Algebra

/-- The quotient of a commutative ring by the kernel of its map to a field. -/
abbrev residueImage (Λ : Type u) (k : Type v) [CommRing Λ] [Field k] [Algebra Λ k] : Type u :=
  Λ ⧸ RingHom.ker (algebraMap Λ k)

variable {Λ : Type u} {k : Type v} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The kernel of the algebra map to a field is maximal when the field is integral over the base ring. -/
instance residueImage.instIsMaximal [Algebra.IsIntegral Λ k] :
    (RingHom.ker (algebraMap Λ k)).IsMaximal :=
  ker_algebraMap_isMaximal_of_isIntegral Λ k

/-- The quotient by the kernel of an integral map to a field is a field. -/
noncomputable instance residueImage.instField [Algebra.IsIntegral Λ k] :
    Field (residueImage Λ k) :=
  Ideal.Quotient.field _

/-- The quotient `residueImage Λ k` acts on `k` through the induced map. -/
instance residueImage.instAlgebra : Algebra (residueImage Λ k) k :=
  (RingHom.kerLift (algebraMap Λ k)).toAlgebra

/-- The scalar actions on `k` form a tower through `residueImage Λ k`. -/
instance residueImage.instIsScalarTower : IsScalarTower Λ (residueImage Λ k) k :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- Finiteness of `k` over `Λ` descends to finiteness over `residueImage Λ k`. -/
instance residueImage.instFinite [Module.Finite Λ k] :
    Module.Finite (residueImage Λ k) k :=
  Module.Finite.of_restrictScalars_finite Λ (residueImage Λ k) k

/-- The vector-space degree over the image subalgebra equals the degree over the residue image. -/
theorem finrank_range_eq_finrank_residueImage :
    Module.finrank (Algebra.ofId Λ k).range k =
      Module.finrank (residueImage Λ k) k := sorry

end Algebra
