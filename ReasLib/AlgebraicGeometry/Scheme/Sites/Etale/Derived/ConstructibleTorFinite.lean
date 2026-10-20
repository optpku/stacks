/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Derived.TorDimension
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v r

namespace AlgebraicGeometry.Scheme

/-- The full subcategory of a cohomology-in derived category cut out by a supplied
object property on the ambient derived category. -/
abbrev EtaleConstructibleTorFinite (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [IsNoetherianRing Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ U : X.Etale, HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    (constructible : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (locallyFiniteTorDimension :
      ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))) :=
  ObjectProperty.FullSubcategory
    (fun K : DerivedCategory.CohomologyIn constructible ↦ locallyFiniteTorDimension K.obj)

namespace Etale.Derived

variable (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/-- Constructible module sheaves on the small étale site, defined by finite-type local
constancy on finite constructible locally closed stratifications of affine opens. -/
def constructibleModule : ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)) :=
  Sheaf.IsConstructibleEtaleModule
    (fun {Y} f ↦ ((Scheme.smallEtalePullback f).sheafPullback
      (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
    (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
      Sheaf.IsFiniteTypeLocallyConstantModule G)

variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale,
  HasDerivedCategory.{r} (Sheaf (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ))]
variable [∀ U : X.Etale, ((X.smallEtaleTopology.over U).W (A := ModuleCat.{v} Λ)).IsMonoidal]

/-- Derived étale module sheaves with constructible cohomology in every degree and locally
finite Tor dimension. -/
def constructibleTorFinite :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :=
  fun K ↦ DerivedCategory.cohomologyIn (constructibleModule X Λ) K ∧
    Sheaf.ModuleDerived.locallyFiniteTorDimension X.smallEtaleTopology Λ K

/-- The full subcategory of the étale derived category consisting of objects with
constructible cohomology and locally finite Tor dimension. -/
abbrev ConstructibleTorFinite := (constructibleTorFinite X Λ).FullSubcategory

/-- Membership in the constructible Tor-finite property is constructibility of every
cohomology sheaf together with covering-local bounded flat representatives. -/
theorem constructibleTorFinite_iff
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :
    constructibleTorFinite X Λ K ↔
      (∀ degree : ℤ, constructibleModule X Λ
        ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))
          degree).obj K)) ∧
      (∀ U : X.Etale, ∃ cover : X.smallEtaleTopology.Cover U, ∀ member : cover.Arrow,
        ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.HasFlatRepresentativeIn
          ((Sheaf.ModuleDerived.overPullback X.smallEtaleTopology Λ member.Y).obj K) a b) := sorry

namespace ConstructibleTorFinite

/-- The full inclusion of constructible Tor-finite derived objects into the category of
derived objects with constructible cohomology. -/
def toConstructible :
    ConstructibleTorFinite X Λ ⥤ DerivedCategory.CohomologyIn (constructibleModule X Λ) :=
  ObjectProperty.ιOfLE (fun _ membership ↦ membership.1)

/-- A constructible Tor-finite derived object has locally finite Tor dimension. -/
theorem locallyFiniteTorDimension (K : ConstructibleTorFinite X Λ) :
    Sheaf.ModuleDerived.locallyFiniteTorDimension X.smallEtaleTopology Λ K.obj := sorry

/-- Every cohomology sheaf of a constructible Tor-finite derived object is constructible. -/
theorem homology_mem (K : ConstructibleTorFinite X Λ) (degree : ℤ) :
    constructibleModule X Λ
      ((DerivedCategory.homologyFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))
        degree).obj K.obj) := sorry

end ConstructibleTorFinite

end Etale.Derived

end AlgebraicGeometry.Scheme
