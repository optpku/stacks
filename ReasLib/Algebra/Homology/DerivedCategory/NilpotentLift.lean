/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomotopyCategory.KProjective
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Additive
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleEmbedding
public import ReasLib.RingTheory.Algebra.TensorProduct.RightAlgebra

/-!
# Flat module lifts versus bounded-above derived lifts

Over a nilpotent ring quotient, relative flat module liftability is equivalent to
bounded-above derived liftability after a flat algebra base change.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct Algebra.TensorProduct.Right

universe u

namespace CategoryTheory.ModuleCat.NilpotentLift

/-- Existence of an `A'`-flat `P'`-module `M'` with
`(ModuleCat.extendScalars (algebraMap P' P)).obj M'` isomorphic to `M`. -/
def existsFlatLift (A' : Type u) [CommRing A'] (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P] [Algebra A' P']
    (M : ModuleCat.{u} P) : Prop :=
  ∃ M' : ModuleCat.{u} P',
    Module.Flat A' ((ModuleCat.restrictScalars (algebraMap A' P')).obj M') ∧
      IsIsomorphic ((ModuleCat.extendScalars (algebraMap P' P)).obj M') M

/-- Flat liftability is equivalent to the existence of a relatively flat module whose
extension of scalars is isomorphic to the given module. -/
theorem existsFlatLift_iff (A' : Type u) [CommRing A'] (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P] [Algebra A' P']
    (M : ModuleCat.{u} P) :
    existsFlatLift A' P' M ↔
      ∃ M' : ModuleCat.{u} P',
        Module.Flat A' ((ModuleCat.restrictScalars (algebraMap A' P')).obj M') ∧
          IsIsomorphic ((ModuleCat.extendScalars (algebraMap P' P)).obj M') M :=
  sorry

/-- Existence of a bounded-above complex of projective `P'`-modules whose termwise
extension of scalars to `P` represents the degree-zero derived object of `M`. -/
def existsBoundedAboveDerivedLift (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P]
    (M : ModuleCat.{u} P) : Prop :=
  ∃ complex : CochainComplex (ModuleCat.{u} P') ℤ, ∃ upperBound : ℤ,
    complex.IsStrictlyLE upperBound ∧
      (∀ degree : ℤ, Projective (complex.X degree)) ∧
        IsIsomorphic
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars (algebraMap P' P)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj complex))
          (single0 M)

/-- Bounded-above derived liftability is equivalent to the existence of a strictly
bounded-above, termwise projective cochain complex whose scalar extension represents the
degree-zero derived module. -/
theorem existsBoundedAboveDerivedLift_iff (P' : Type u) {P : Type u}
    [CommRing P'] [CommRing P] [Algebra P' P]
    (M : ModuleCat.{u} P) :
    existsBoundedAboveDerivedLift P' M ↔
      ∃ complex : CochainComplex (ModuleCat.{u} P') ℤ, ∃ upperBound : ℤ,
        complex.IsStrictlyLE upperBound ∧
          (∀ degree : ℤ, Projective (complex.X degree)) ∧
            IsIsomorphic
              (DerivedCategory.Q.obj
                (((ModuleCat.extendScalars (algebraMap P' P)).mapHomologicalComplex
                  (ComplexShape.up ℤ)).obj complex))
              (single0 M) :=
  sorry

/-- If `A' → A` is surjective with nilpotent kernel, `A' → P'` is flat, and `M` is an
`A`-flat module over `P' ⊗[A'] A`, then an `A'`-flat `P'`-module lift of `M` exists if and
only if a bounded-above derived extension lift of `single0 M` exists. -/
theorem existsFlatLift_iff_existsBoundedAboveDerivedLift
    {A' A P' : Type u} [CommRing A'] [CommRing A] [CommRing P']
    [Algebra A' A] [Algebra A' P'] [Module.Flat A' P']
    (hsurj : Function.Surjective (algebraMap A' A))
    (hker : IsNilpotent (RingHom.ker (algebraMap A' A)))
    (M : ModuleCat.{u} (P' ⊗[A'] A))
    (hMflat : Module.Flat A
      ((ModuleCat.restrictScalars (algebraMap A (P' ⊗[A'] A))).obj M)) :
    existsFlatLift A' P' M ↔ existsBoundedAboveDerivedLift P' M :=
  sorry

end CategoryTheory.ModuleCat.NilpotentLift

end
