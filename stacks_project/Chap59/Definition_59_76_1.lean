module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.Tactic.CrossRefAttribute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]

/-- A full subcategory of the étale derived category whose cohomology objects satisfy
an object property on sheaves of modules. -/
abbrev EtaleConstructibleCategory (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [IsNoetherianRing Λ]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{v} Λ)]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
    [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
    (constructible : ObjectProperty
      (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :
    Type _ :=
  (DerivedCategory.cohomologyIn constructible).FullSubcategory

section canonical_check

variable [∀ Y : Scheme.{u},
  HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z)
  (P : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]

/- Definition 59.76.1: for a scheme `X` and a Noetherian ring `Λ`, the category
`D_c(Xₑₜ, Λ)` is the full subcategory of the derived category of sheaves of
`Λ`-modules on the small étale site whose cohomology sheaves are constructible
`Λ`-modules. -/
@[stacks 095W] #check
  (CategoryTheory.DerivedCategory.CohomologyIn
    (CategoryTheory.Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback
          (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
        CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule G) :
      ObjectProperty (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :
    Type (max (max (u + 1) (v + 1)) (u + 1) (v + 1)))

end canonical_check

end AlgebraicGeometry.Scheme
