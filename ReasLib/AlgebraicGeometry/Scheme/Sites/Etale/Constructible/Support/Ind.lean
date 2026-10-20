/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Support
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Ind
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Torsion
public import Mathlib.Topology.Sets.Closeds

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry
open TopologicalSpace

universe u

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}} [IsNoetherian X]

/-- A locally torsion abelian étale sheaf supported in a specialization-stable subset is a
filtered colimit of constructible sheaves whose supports lie in closed subsets of that subset. -/
theorem isConstructibleEtaleAddCommGrp_ind_of_support
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    {E : Set X} (hE : StableUnderSpecialization E)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F) (hsupp : abelianSheafSupport F ⊆ E) :
    ObjectProperty.ind.{u + 1}
      (fun G ↦ IsConstructibleEtaleAddCommGrp
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) G ∧
        ∃ Z : Set X, IsClosed Z ∧ Z ⊆ E ∧ abelianSheafSupport G ⊆ Z) F := sorry

/-- A sheaf of modules over a Noetherian ring supported in a specialization-stable subset is a
filtered colimit of constructible sheaves whose supports lie in closed subsets of that subset. -/
theorem isConstructibleEtaleModule_ind_of_support
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    {E : Set X} (hE : StableUnderSpecialization E)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hsupp : moduleSheafSupport F ⊆ E) :
    ObjectProperty.ind.{u + 1}
      (fun G ↦ IsConstructibleEtaleModule
        (fun {Y} f ↦
          ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
            X.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) G ∧
        ∃ Z : Set X, IsClosed Z ∧ Z ⊆ E ∧ moduleSheafSupport G ⊆ Z) F := sorry

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]

/-- Constructible étale abelian sheaves whose support is contained in a closed subset avoiding a
specified point `η`. -/
def IsConstructibleEtaleAddCommGrp.SupportAway
    (η : X) :
    ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  fun G ↦ IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) G ∧
    ∃ Z : Closeds X, η ∉ Z ∧ abelianSheafSupport G ⊆ (Z : Set X)

/-- The support-away property for constructible étale abelian sheaves unfolds to constructibility
and containment of the support in a closed subset avoiding `η`. -/
theorem IsConstructibleEtaleAddCommGrp.SupportAway_iff
    (η : X) (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsConstructibleEtaleAddCommGrp.SupportAway η G ↔
      IsConstructibleEtaleAddCommGrp
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) G ∧
        ∃ Z : Closeds X, η ∉ Z ∧ abelianSheafSupport G ⊆ (Z : Set X) :=
  sorry

/-- A locally torsion abelian étale sheaf with zero geometric stalk at a generic point is a
filtered colimit of constructible sheaves supported in closed subsets avoiding that point. -/
theorem isConstructibleEtaleAddCommGrp_ind_supportAway
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    (ηbar : Scheme.GeometricPoint X)
    (hη : IsGenericPoint ηbar.image (irreducibleComponent ηbar.image))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsLocallyTorsion F)
    (h0 : IsZero (geometricStalkAddCommGrp F ηbar)) :
    ObjectProperty.ind.{u + 1}
      (IsConstructibleEtaleAddCommGrp.SupportAway ηbar.image) F :=
  sorry

/-- Constructible étale module sheaves whose support is contained in a closed subset avoiding a
specified point `η`. -/
def IsConstructibleEtaleModule.SupportAway
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    (η : X) :
    ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  fun G ↦ IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) G ∧
    ∃ Z : Closeds X, η ∉ Z ∧ moduleSheafSupport G ⊆ (Z : Set X)

/-- The support-away property for constructible étale module sheaves unfolds to constructibility
and containment of the support in a closed subset avoiding `η`. -/
theorem IsConstructibleEtaleModule.SupportAway_iff
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    (η : X) (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsConstructibleEtaleModule.SupportAway η G ↔
      IsConstructibleEtaleModule
          (fun {Y} f ↦
            ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
              X.smallEtaleTopology Y.smallEtaleTopology).obj)
          (fun {Y} G ↦ IsFiniteTypeLocallyConstantModule G) G ∧
        ∃ Z : Closeds X, η ∉ Z ∧ moduleSheafSupport G ⊆ (Z : Set X) :=
  sorry

/-- A module sheaf with zero geometric stalk at a generic point is a filtered colimit of
constructible sheaves supported in closed subsets avoiding that point. -/
theorem isConstructibleEtaleModule_ind_supportAway
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)]
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u + 1} Λ)]
    [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
      (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
    (ηbar : Scheme.GeometricPoint X)
    (hη : IsGenericPoint ηbar.image (irreducibleComponent ηbar.image))
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h0 : IsZero (geometricStalkModule F ηbar)) :
    ObjectProperty.ind.{u + 1}
      (IsConstructibleEtaleModule.SupportAway ηbar.image) F :=
  sorry

end CategoryTheory.Sheaf
