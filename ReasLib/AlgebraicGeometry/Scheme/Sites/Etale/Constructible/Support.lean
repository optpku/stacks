/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Topology

universe u

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/-- The geometric stalk of a set-valued small-étale sheaf at a geometric point. -/
noncomputable def geometricStalkSet
    (F : Sheaf X.smallEtaleTopology (Type (u + 1)))
    (xbar : Scheme.GeometricPoint X) : Type (u + 1) :=
  (@Scheme.pointSmallEtale X xbar.K inferInstance
      (@IsSepClosed.of_isAlgClosed xbar.K inferInstance xbar.isAlgClosed) xbar.hom).presheafFiber.obj F.1

/-- The geometric set stalk is the associated small-étale presheaf fiber. -/
theorem geometricStalkSet_def
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) (xbar : Scheme.GeometricPoint X) :
    geometricStalkSet F xbar =
      (@Scheme.pointSmallEtale X xbar.K inferInstance
        (@IsSepClosed.of_isAlgClosed xbar.K inferInstance xbar.isAlgClosed)
        xbar.hom).presheafFiber.obj F.1 := sorry

/-- The map induced on geometric set stalks by a morphism of étale sheaves. -/
noncomputable def geometricStalkMap
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (xbar : Scheme.GeometricPoint X) : geometricStalkSet F xbar → geometricStalkSet G xbar :=
  (@Scheme.pointSmallEtale X xbar.K inferInstance
      (@IsSepClosed.of_isAlgClosed xbar.K inferInstance xbar.isAlgClosed)
      xbar.hom).presheafFiber.map φ.hom

/-- The geometric stalk map is the presheaf-fiber action of the sheaf morphism. -/
theorem geometricStalkMap_apply
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (xbar : Scheme.GeometricPoint X) (a : geometricStalkSet F xbar) :
    geometricStalkMap φ xbar a =
      (@Scheme.pointSmallEtale X xbar.K inferInstance
        (@IsSepClosed.of_isAlgClosed xbar.K inferInstance xbar.isAlgClosed)
        xbar.hom).presheafFiber.map φ.hom a := sorry

/-- The locus of scheme points at which a geometric stalk map is surjective. -/
noncomputable def surjectiveStalkLocus
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G) : Set X :=
  {x | ∃ xbar : Scheme.GeometricPoint X,
    xbar.image = x ∧ Function.Surjective (geometricStalkMap φ xbar)}

/-- Membership in the surjective geometric-stalk locus. -/
theorem mem_surjectiveStalkLocus_iff
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G) (x : X) :
    x ∈ surjectiveStalkLocus φ ↔
      ∃ xbar : Scheme.GeometricPoint X,
        xbar.image = x ∧ Function.Surjective (geometricStalkMap φ xbar) := sorry

/-- Surjectivity of a geometric stalk map depends only on the image of its geometric point. -/
theorem surjective_geometricStalkMap_iff_of_image_eq
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (xbar ybar : Scheme.GeometricPoint X) (himage : xbar.image = ybar.image) :
    Function.Surjective (geometricStalkMap φ xbar) ↔
      Function.Surjective (geometricStalkMap φ ybar) := sorry

/-- The locus of scheme points at which a geometric stalk map is injective. -/
noncomputable def injectiveStalkLocus
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G) : Set X :=
  {x | ∃ xbar : Scheme.GeometricPoint X,
    xbar.image = x ∧ Function.Injective (geometricStalkMap φ xbar)}

/-- Membership in the injective geometric-stalk locus. -/
theorem mem_injectiveStalkLocus_iff
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G) (x : X) :
    x ∈ injectiveStalkLocus φ ↔
      ∃ xbar : Scheme.GeometricPoint X,
        xbar.image = x ∧ Function.Injective (geometricStalkMap φ xbar) := sorry

/-- Injectivity of a geometric stalk map depends only on the image of its geometric point. -/
theorem injective_geometricStalkMap_iff_of_image_eq
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (xbar ybar : Scheme.GeometricPoint X) (himage : xbar.image = ybar.image) :
    Function.Injective (geometricStalkMap φ xbar) ↔
      Function.Injective (geometricStalkMap φ ybar) := sorry

/-- The locus where a geometric stalk map is isomorphic to a prescribed map of sets. -/
noncomputable def isoToMapStalkLocus
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    {A B : Type (u + 1)} (f : A → B) : Set X :=
  {x | ∃ xbar : Scheme.GeometricPoint X, xbar.image = x ∧
    ∃ eF : geometricStalkSet F xbar ≃ A, ∃ eG : geometricStalkSet G xbar ≃ B,
      eG ∘ geometricStalkMap φ xbar = f ∘ eF}

/-- Membership in the prescribed-map geometric-stalk locus. -/
theorem mem_isoToMapStalkLocus_iff
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    {A B : Type (u + 1)} (f : A → B) (x : X) :
    x ∈ isoToMapStalkLocus φ f ↔
      ∃ xbar : Scheme.GeometricPoint X, xbar.image = x ∧
        ∃ eF : geometricStalkSet F xbar ≃ A, ∃ eG : geometricStalkSet G xbar ≃ B,
          eG ∘ geometricStalkMap φ xbar = f ∘ eF := sorry

/-- Being isomorphic to a prescribed map at geometric stalks depends only on the image point. -/
theorem isoToMap_geometricStalkMap_iff_of_image_eq
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    {A B : Type (u + 1)} (f : A → B)
    (xbar ybar : Scheme.GeometricPoint X) (himage : xbar.image = ybar.image) :
    (∃ eF : geometricStalkSet F xbar ≃ A, ∃ eG : geometricStalkSet G xbar ≃ B,
        eG ∘ geometricStalkMap φ xbar = f ∘ eF) ↔
      ∃ eF : geometricStalkSet F ybar ≃ A, ∃ eG : geometricStalkSet G ybar ≃ B,
        eG ∘ geometricStalkMap φ ybar = f ∘ eF := sorry

/-- The surjective geometric-stalk locus of a constructible étale sheaf morphism is constructible. -/
theorem isConstructible_surjectiveStalkLocus
    [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F)
    (hG : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) G) :
    Topology.IsConstructible (surjectiveStalkLocus φ) := sorry

/-- The injective geometric-stalk locus of a constructible étale sheaf morphism is constructible. -/
theorem isConstructible_injectiveStalkLocus
    [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F)
    (hG : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) G) :
    Topology.IsConstructible (injectiveStalkLocus φ) := sorry

/-- The prescribed-map geometric-stalk locus of a constructible étale sheaf morphism is constructible. -/
theorem isConstructible_isoToMapStalkLocus
    [CompactSpace X] [QuasiSeparatedSpace X]
    {F G : Sheaf X.smallEtaleTopology (Type (u + 1))} (φ : F ⟶ G)
    {A B : Type (u + 1)} (f : A → B)
    (hF : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) F)
    (hG : IsConstructibleEtaleSet
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (Type (u + 1))
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstant G) G) :
    Topology.IsConstructible (isoToMapStalkLocus φ f) := sorry

/-- The geometric stalk of an abelian sheaf on the small étale site. -/
noncomputable def geometricStalkAddCommGrp
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (xbar : Scheme.GeometricPoint X) : AddCommGrpCat.{u + 1} :=
  (@Scheme.pointSmallEtale X xbar.K inferInstance
      (@IsSepClosed.of_isAlgClosed xbar.K inferInstance xbar.isAlgClosed) xbar.hom).presheafFiber.obj F.1

/-- The support of an abelian étale sheaf is the locus of nonzero geometric stalks. -/
noncomputable def abelianSheafSupport
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) : Set X :=
  {s | ∃ sbar : Scheme.GeometricPoint X,
    sbar.image = s ∧ ¬ IsZero (geometricStalkAddCommGrp F sbar)}

/-- Membership in abelian sheaf support is existence of a nonzero geometric stalk over the point. -/
theorem mem_abelianSheafSupport_iff
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (s : X) :
    s ∈ abelianSheafSupport F ↔
      ∃ sbar : Scheme.GeometricPoint X,
        sbar.image = s ∧ ¬ IsZero (geometricStalkAddCommGrp F sbar) := sorry

/-- The zero property of an abelian geometric stalk depends only on the image point. -/
theorem geometricStalkAddCommGrp_isZero_iff_of_image_eq
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (sbar tbar : Scheme.GeometricPoint X) (himage : sbar.image = tbar.image) :
    IsZero (geometricStalkAddCommGrp F sbar) ↔ IsZero (geometricStalkAddCommGrp F tbar) := sorry

/-- The support of a constructible abelian étale sheaf is constructible. -/
theorem isConstructible_abelianSheafSupport
    [CompactSpace X] [QuasiSeparatedSpace X]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : IsConstructibleEtaleAddCommGrp
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (AddCommGrpCat.{u + 1})
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G) F) :
    Topology.IsConstructible (abelianSheafSupport F) := sorry

/-- The geometric stalk of a sheaf of modules, regarded as an additive-group object. -/
noncomputable def geometricStalkModule
    {Λ : Type (u + 1)} [Ring Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (xbar : Scheme.GeometricPoint X) : AddCommGrpCat.{u + 1} :=
  (@Scheme.pointSmallEtale X xbar.K inferInstance
      (@IsSepClosed.of_isAlgClosed xbar.K inferInstance xbar.isAlgClosed) xbar.hom).presheafFiber.obj
    (F.1 ⋙ forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})

/-- The support of an étale sheaf of modules is the locus of nonzero forgotten geometric stalks. -/
noncomputable def moduleSheafSupport
    {Λ : Type (u + 1)} [Ring Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) : Set X :=
  {s | ∃ sbar : Scheme.GeometricPoint X,
    sbar.image = s ∧ ¬ IsZero (geometricStalkModule F sbar)}

/-- Membership in module sheaf support is existence of a nonzero geometric stalk over the point. -/
theorem mem_moduleSheafSupport_iff
    {Λ : Type (u + 1)} [Ring Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (s : X) :
    s ∈ moduleSheafSupport F ↔
      ∃ sbar : Scheme.GeometricPoint X,
        sbar.image = s ∧ ¬ IsZero (geometricStalkModule F sbar) := sorry

/-- The zero property of a module geometric stalk depends only on the image point. -/
theorem geometricStalkModule_isZero_iff_of_image_eq
    {Λ : Type (u + 1)} [Ring Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (sbar tbar : Scheme.GeometricPoint X) (himage : sbar.image = tbar.image) :
    IsZero (geometricStalkModule F sbar) ↔ IsZero (geometricStalkModule F tbar) := sorry

/-- The support of a constructible sheaf of modules over a Noetherian ring is constructible. -/
theorem isConstructible_moduleSheafSupport
    [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [Ring Λ] [IsNoetherianRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{u + 1} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F) :
    Topology.IsConstructible (moduleSheafSupport F) := sorry

end CategoryTheory.Sheaf
