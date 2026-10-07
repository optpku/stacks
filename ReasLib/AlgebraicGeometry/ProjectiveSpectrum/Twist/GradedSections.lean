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

/-- An explicit presentation of the sheaves associated to the integral twists of a graded
module, together with the canonical maps from its homogeneous pieces to global sections. -/
@[stacks 0AG1 "associated-module twist presentation"]
structure Proj.AssociatedModule.Presentation (Mpiece : ℤ → Type u)
    [∀ n : ℤ, AddCommGroup (Mpiece n)] where
  /-- The integral family whose degree-`n` term is the sheaf associated to the `n`th twist of
  the graded module. -/
  associatedTwist : ProjTwistFamily 𝒜
  /-- The canonical additive map from each homogeneous piece to the global sections of its
  associated twist. -/
  sectionMap : ∀ n : ℤ, Mpiece n →+ Γ(associatedTwist n, ⊤)

namespace Proj.AssociatedModule.Presentation

variable {𝒜}
variable {Mpiece : ℤ → Type u} [∀ n : ℤ, AddCommGroup (Mpiece n)]

/-- Build an associated-twist presentation from an explicit family and its degreewise maps to
global sections. -/
@[stacks 0AG3 "associated-module twist presentation from a family"]
def ofFamily (associatedTwist : ProjTwistFamily 𝒜)
    (sectionMap : ∀ n : ℤ, Mpiece n →+ Γ(associatedTwist n, ⊤)) :
    Proj.AssociatedModule.Presentation 𝒜 Mpiece where
  associatedTwist := associatedTwist
  sectionMap := sectionMap

/-- Transport the section map in one degree from the associated twist to an explicitly
isomorphic module sheaf. -/
@[stacks 0AG3 "transport an associated-module section map across an isomorphism"]
def sectionMapOfIso (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    {n : ℤ} {F : (Proj 𝒜).Modules} (e : F ≅ P.associatedTwist n) :
    Mpiece n →+ Γ(F, ⊤) :=
  (Scheme.Modules.globalSectionsMap e.inv).hom.comp (P.sectionMap n)

/-- The transported section map applies the original section map and then the map on global
sections induced by the inverse isomorphism. -/
@[simp, stacks 0AG3 "transported associated-module section map formula"]
theorem sectionMapOfIso_apply (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    {n : ℤ} {F : (Proj 𝒜).Modules} (e : F ≅ P.associatedTwist n) (m : Mpiece n) :
    sectionMapOfIso P e m =
      (Scheme.Modules.globalSectionsMap e.inv).hom (P.sectionMap n m) := sorry

/-- The degreewise section maps commute with multiplication by homogeneous scalars. -/
@[stacks 0AG3 "graded associated-module section presentation"]
def IsGraded (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))] : Prop :=
  ∀ {d : ℕ} {n : ℤ} (a : 𝒜 d) (m : Mpiece n),
    P.sectionMap (d +ᵥ n)
        (GradedMonoid.GSMul.smul (A := fun e : ℕ ↦ 𝒜 e) (M := Mpiece) a m) =
      GradedMonoid.GSMul.smul (A := fun e : ℕ ↦ 𝒜 e)
        (M := fun i : ℤ ↦ Γ(P.associatedTwist i, ⊤)) a (P.sectionMap n m)


/-- The direct sum of the canonical degreewise section maps commutes with the graded scalar
action. -/
@[stacks 01MR "linearity of the graded associated-module section map", stacks 0AG4]
theorem gradedMap_smul (Mpiece : ℤ → Type u) [∀ n : ℤ, AddCommGroup (Mpiece n)]
    (P : Proj.AssociatedModule.Presentation 𝒜 Mpiece)
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d) Mpiece]
    [DirectSum.Gmodule (fun d : ℕ ↦ 𝒜 d)
      (fun n : ℤ ↦ Γ(P.associatedTwist n, ⊤))]
    (hP : P.IsGraded) (a : ⨁ d : ℕ, 𝒜 d) (m : ⨁ n : ℤ, Mpiece n) :
    DirectSum.map (fun n ↦ P.sectionMap n) (a • m) =
      a • DirectSum.map (fun n ↦ P.sectionMap n) m := sorry

/-- The canonical degreewise section maps assemble to a linear map from a graded module to the
external direct sum of the global sections of its associated twists. -/
@[stacks 01MR "graded associated-module section map", stacks 0AG4]
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
@[simp, stacks 01MR "graded associated-module section map on a summand", stacks 0AG4]
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
