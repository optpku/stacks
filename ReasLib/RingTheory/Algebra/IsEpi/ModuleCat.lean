/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Epi
public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.RingTheory.Algebra.IsEpi.TensorSquare
import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars along algebra epimorphisms

@stack 08YS

An algebra epimorphism is exactly a map for which restriction of scalars on module categories is
fully faithful, provided the target ring is small in the module universe. The forward implication
holds in every module universe. The public criterion keeps `Nonempty FullyFaithful` as the source-facing
proposition, while the `Full` instance is exposed separately so ordinary typeclass-driven module
arguments do not need local instance reconstruction.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe u v w

namespace Algebra.IsEpi

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- An epic algebra makes restriction of scalars full on module categories. -/
@[stacks 08YS "restriction full"]
instance full_of_isEpi [Algebra.IsEpi R S] :
    (ModuleCat.restrictScalars.{w} (algebraMap R S)).Full where
  map_surjective := by
    intro M N f
    let fR : M →ₗ[R] N := f.hom
    let p : S ⊗[R] M →ₗ[R] N :=
      ((TensorProduct.lid' R S N).toLinearMap.restrictScalars R).comp
        (_root_.TensorProduct.map (LinearMap.id : S →ₗ[R] S) fR)
    refine ⟨ModuleCat.ofHom (X := M) (Y := N)
      { toFun := f.hom
        map_add' := f.hom.map_add
        map_smul' := ?_ }, ?_⟩
    · intro s m
      change fR (s • m) = s • fR m
      have h : (1 : S) ⊗ₜ[R] (s • m) = s ⊗ₜ[R] m :=
        (TensorProduct.lid' R S M).injective (by simp)
      simpa [p, fR] using! congrArg p h
    · apply ModuleCat.hom_ext
      rfl

/-- Explicit-hypothesis form of `full_of_isEpi`. This avoids installing a
local typeclass when epimorphy is obtained from ordinary theorem data. -/
@[stacks 08YS "explicit restriction full"]
theorem restrictScalars_full (h : Algebra.IsEpi R S) :
    (ModuleCat.restrictScalars.{w} (algebraMap R S)).Full :=
  @full_of_isEpi R S _ _ _ h

/-- Algebra epimorphy is equivalent to full faithfulness of restriction of scalars when `S`
is small in the module universe. This lets the converse test the tensor square of `S`. -/
@[stacks 08YS "algebra form"]
theorem iff_restrictScalars_fullyFaithful [Small.{w} S] :
    Algebra.IsEpi R S ↔
      Nonempty ((ModuleCat.restrictScalars.{w} (algebraMap R S)).FullyFaithful) := sorry

end Algebra.IsEpi

namespace RingHom

variable {R S : Type u} [CommRing R] [CommRing S]

/-- A commutative-ring epimorphism is exactly a ring map whose restriction-of-scalars functor on
module categories is fully faithful, provided `S` is small in the module universe. -/
@[stacks 08YS]
theorem epi_iff_restrictScalars_fullyFaithful [Small.{w} S] (f : R →+* S) :
    Epi (CommRingCat.ofHom f) ↔
      Nonempty ((ModuleCat.restrictScalars.{w} f).FullyFaithful) := by
  letI : Algebra R S := f.toAlgebra
  exact CommRingCat.epi_iff_epi.trans Algebra.IsEpi.iff_restrictScalars_fullyFaithful

/-- An epimorphic commutative-ring map makes restriction of scalars full. -/
@[stacks 08YS "ring-hom restriction full"]
instance full_of_epi (f : R →+* S) [Epi (CommRingCat.ofHom f)] :
    (ModuleCat.restrictScalars.{w} f).Full := by
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsEpi R S := CommRingCat.epi_iff_epi.mp inferInstance
  exact Algebra.IsEpi.full_of_isEpi

end RingHom
