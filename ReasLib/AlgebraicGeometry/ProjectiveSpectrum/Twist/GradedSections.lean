/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.GradedModule
public import ReasLib.Algebra.Group.Action.NatInt
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Graded sections of integral twist families

This file assembles degreewise maps into the global sections of an integral family of module
sheaves on a projective spectrum.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

universe u v

noncomputable section

namespace AlgebraicGeometry

variable {A : Type u} {σ : Type v} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- A general wrapper for a family of module sheaves and degreewise additive maps to its
sections. This structure imposes no relationship with a graded module. The canonical
associated-module construction is `Proj.AssociatedModule.ShiftedSections.presentation`. -/
structure Proj.AssociatedModule.Presentation (Mpiece : ℤ → Type u)
    [∀ n : ℤ, AddCommGroup (Mpiece n)] where
  /-- The supplied integral family of module sheaves. -/
  associatedTwist : ProjTwistFamily 𝒜
  /-- The supplied additive map in each degree. -/
  sectionMap : ∀ n : ℤ, Mpiece n →+ Γ(associatedTwist n, ⊤)

namespace Proj.AssociatedModule.Presentation

variable {𝒜}
variable {Mpiece : ℤ → Type u} [∀ n : ℤ, AddCommGroup (Mpiece n)]

/-- Package an arbitrary family and arbitrary degreewise additive maps to its sections. -/
def ofFamily (associatedTwist : ProjTwistFamily 𝒜)
    (sectionMap : ∀ n : ℤ, Mpiece n →+ Γ(associatedTwist n, ⊤)) :
    Proj.AssociatedModule.Presentation 𝒜 Mpiece where
  associatedTwist := associatedTwist
  sectionMap := sectionMap

/-- Transport the section map in one degree from the associated twist to an explicitly
isomorphic module sheaf. -/
def sectionMapOfIso (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    {n : ℤ} {F : (Proj 𝒜).Modules} (e : F ≅ P.associatedTwist n) :
    Mpiece n →+ Γ(F, ⊤) :=
  (Scheme.Modules.globalSectionsMap e.inv).hom.comp (P.sectionMap n)

/-- The transported section map applies the original section map and then the map on global
sections induced by the inverse isomorphism. -/
@[simp]
theorem sectionMapOfIso_apply (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    {n : ℤ} {F : (Proj 𝒜).Modules} (e : F ≅ P.associatedTwist n) (m : Mpiece n) :
    sectionMapOfIso P e m =
      (Scheme.Modules.globalSectionsMap e.inv).hom (P.sectionMap n m) := sorry

/-- The degreewise section maps commute with multiplication by homogeneous scalars. -/
def IsGraded (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))] : Prop :=
  ∀ {d : ℕ} {n : ℤ} (a : 𝒜 d) (m : Mpiece n),
    P.sectionMap (d +ᵥ n)
        (GradedMonoid.GSMul.smul (A := fun e : ℕ ↦ 𝒜 e) (M := Mpiece) a m) =
      GradedMonoid.GSMul.smul (A := fun e : ℕ ↦ 𝒜 e)
        (M := fun i : ℤ ↦ Γ(P.associatedTwist i, ⊤)) a (P.sectionMap n m)


/-- Compatible degreewise additive maps commute with the direct-sum scalar action. -/
theorem gradedMap_smul (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
    (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
    (hP : P.IsGraded) (a : ⨁ d : ℕ, 𝒜 d) (m : ⨁ n : ℤ, Mpiece n) :
    DirectSum.map (fun n ↦ P.sectionMap n) (a • m) =
      a • DirectSum.map (fun n ↦ P.sectionMap n) m := sorry

/-- Assemble compatible degreewise additive maps into a linear map of direct sums. -/
def gradedMap (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
    (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
    (hP : P.IsGraded) :
    (⨁ n : ℤ, Mpiece n) →ₗ[(⨁ d : ℕ, 𝒜 d)]
      (⨁ n : ℤ, Γ(P.associatedTwist n, ⊤)) :=
  { DirectSum.map (fun n ↦ P.sectionMap n) with
    map_smul' := gradedMap_smul Mpiece P hP }

/-- On a homogeneous generator, `gradedMap` applies the map in that degree and includes
the result in the same direct-sum component. -/
@[simp]
theorem gradedMap_of (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
    (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
    (hP : P.IsGraded)
    (n : ℤ) (m : Mpiece n) :
    gradedMap Mpiece P hP (DirectSum.of Mpiece n m) =
      DirectSum.of (fun i : ℤ ↦ Γ(P.associatedTwist i, ⊤)) n (P.sectionMap n m) := sorry

end Proj.AssociatedModule.Presentation

end AlgebraicGeometry
