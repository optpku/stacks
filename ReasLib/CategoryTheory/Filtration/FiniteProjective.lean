/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod
public import ReasLib.CategoryTheory.Filtration.Finite
public import ReasLib.RingTheory.Finiteness.Projective
public import ReasLib.CategoryTheory.Filtration.GradedPiece
public import ReasLib.CategoryTheory.Filtration.ZeroObject
public import ReasLib.CategoryTheory.Filtration.Functors

/-!
# Filtered finite projective objects

A filtered left module is filtered finite projective when all its associated
graded pieces are finite projective. Graded pieces and the underlying module of
a finite filtered finite-projective object are finite and projective.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject FilteredObject.Finite

universe u v

namespace CategoryTheory.FilteredObject

variable {R : Type u} [Ring R]

/-- A filtered left `R`-module is filtered finite projective when every associated
graded piece is a finite projective `R`-module. -/
class IsFilteredFiniteProjective (P : FilteredObject (ModuleCat.{v} R)) : Prop where
  /-- Every graded piece of a filtered finite-projective object is finite projective. -/
  finiteProjective (p : ℤ) : Module.FiniteProjective R (P.gradedPiece p)

/-- Filtered finite-projectivity is equivalent to finite projectivity of every
associated graded piece. -/
theorem isFilteredFiniteProjective_iff {P : FilteredObject (ModuleCat.{v} R)} :
    IsFilteredFiniteProjective P ↔ ∀ p, Module.FiniteProjective R (P.gradedPiece p) :=
  ⟨fun h ↦ h.finiteProjective, fun h ↦ ⟨h⟩⟩

/-- Filtered finite-projectivity transports across an isomorphism of filtered objects. -/
theorem IsFilteredFiniteProjective.of_iso {P Q : FilteredObject (ModuleCat.{v} R)}
    (e : P ≅ Q) (hQ : IsFilteredFiniteProjective Q) :
    IsFilteredFiniteProjective P := by
  refine ⟨fun p ↦ ?_⟩
  let e' : P.gradedPiece p ≅ Q.gradedPiece p := ((associatedGradedFunctor :
    FilteredObject (ModuleCat.{v} R) ⥤ _) ⋙ GradedObject.eval p).mapIso e
  letI : Module.Finite R (Q.gradedPiece p) := (hQ.finiteProjective p).finite
  letI : Module.Projective R (Q.gradedPiece p) := (hQ.finiteProjective p).projective
  exact ⟨Module.Finite.equiv e'.symm.toLinearEquiv,
    Module.Projective.of_equiv e'.symm.toLinearEquiv⟩

/-- The zero filtered module is filtered finite projective. -/
noncomputable instance instIsFilteredFiniteProjectiveZero :
    IsFilteredFiniteProjective (0 : FilteredObject (ModuleCat.{v} R)) := by
  refine ⟨fun p ↦ ?_⟩
  let F := (associatedGradedFunctor :
    FilteredObject (ModuleCat.{v} R) ⥤ _) ⋙ GradedObject.eval p
  letI : Subsingleton ((0 : FilteredObject (ModuleCat.{v} R)).gradedPiece p) :=
    ModuleCat.subsingleton_of_isZero (F.map_isZero (isZero_zero _))
  exact ⟨inferInstance, inferInstance⟩

/-- Graded pieces of a filtered finite-projective object are finite modules. -/
instance instFinite_gradedPiece (P : FilteredObject (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P] (p : ℤ) :
    Module.Finite R (P.gradedPiece p) :=
  (IsFilteredFiniteProjective.finiteProjective (P := P) p).finite

/-- Graded pieces of a filtered finite-projective object are projective modules. -/
instance instProjective_gradedPiece (P : FilteredObject (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P] (p : ℤ) :
    Module.Projective R (P.gradedPiece p) :=
  (IsFilteredFiniteProjective.finiteProjective (P := P) p).projective

namespace Finite

private theorem finiteProjective_of_mono {M N : ModuleCat.{v} R} (f : M ⟶ N) [Mono f]
    (hM : Module.FiniteProjective R M)
    (hQ : Module.FiniteProjective R (cokernel f : ModuleCat.{v} R)) :
    Module.FiniteProjective R N := by
  letI : Module.Finite R M := hM.finite
  letI : Module.Projective R M := hM.projective
  letI : Module.Finite R (cokernel f : ModuleCat.{v} R) := hQ.finite
  letI : Module.Projective R (cokernel f : ModuleCat.{v} R) := hQ.projective
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (cokernel.π f).hom LinearMap.id
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  let e : (M × (cokernel f : ModuleCat.{v} R)) ≃ₗ[R] N := lequivProdOfRightSplitExact
    ((ModuleCat.mono_iff_injective f).mp inferInstance)
    (ShortComplex.cokernelSequence_exact f).moduleCat_range_eq_ker hs
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

private theorem underlying_finiteProjective (P : category (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P.obj] :
    Module.FiniteProjective R ((Forget.functor (ModuleCat.{v} R)).obj P) := by
  obtain ⟨a, b, ha, hb⟩ := P.property
  have hstage (n : ℕ) : Module.FiniteProjective R (P.obj.stage (b - n)) := by
    induction n with
    | zero =>
      rw [Nat.cast_zero, sub_zero]
      have hz : IsZero (P.obj.stage b) := by
        change IsZero (P.obj.filtration.stage b : ModuleCat.{v} R)
        rw [hb]
        exact (isZero_zero _).of_iso Subobject.botCoeIsoZero
      letI : Subsingleton (P.obj.stage b) := ModuleCat.subsingleton_of_isZero hz
      exact ⟨inferInstance, inferInstance⟩
    | succ n ih =>
      let p : ℤ := b - (↑(n + 1) : ℤ)
      have he : p + 1 = b - n := by dsimp [p]; omega
      change Module.FiniteProjective R (P.obj.stage p)
      exact finiteProjective_of_mono
        (M := P.obj.stage (p + 1)) (N := P.obj.stage p) (P.obj.succInclusion p)
        (by rw [he]; exact ih)
        (IsFilteredFiniteProjective.finiteProjective (P := P.obj) p)
  have ha' : P.obj.filtration.stage (min a b) = ⊤ := by
    apply top_unique
    rw [← ha]
    exact P.obj.filtration.stage_mono (min_le_left a b)
  have hn : b - (↑((b - min a b).toNat) : ℤ) = min a b := by omega
  have hA : Module.FiniteProjective R (P.obj.stage (min a b)) := by
    have h := hstage (b - min a b).toNat
    rw [hn] at h
    exact h
  letI : Module.Finite R (P.obj.stage (min a b)) := hA.finite
  letI : Module.Projective R (P.obj.stage (min a b)) := hA.projective
  letI : IsIso (P.obj.filtration.stage (min a b)).arrow :=
    (Subobject.isIso_arrow_iff_eq_top _).mpr ha'
  let e := (asIso (P.obj.filtration.stage (min a b)).arrow).toLinearEquiv
  exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩

/-- The underlying module of a finite filtered finite-projective object is finite. -/
instance instFinite (P : category (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P.obj] :
    Module.Finite R ((Forget.functor (ModuleCat.{v} R)).obj P) :=
  (underlying_finiteProjective P).finite

/-- The underlying module of a finite filtered finite-projective object is projective. -/
instance instProjective (P : category (ModuleCat.{v} R))
    [IsFilteredFiniteProjective P.obj] :
    Module.Projective R ((Forget.functor (ModuleCat.{v} R)).obj P) :=
  (underlying_finiteProjective P).projective

end Finite

end CategoryTheory.FilteredObject
