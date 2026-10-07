module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ExtensionByZero.Exactness
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory

noncomputable section

universe u v r

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable (X : Scheme.{u}) (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]

/-- The object property of derived étale module sheaves whose cohomology in every
integer degree is constructible, using finite-type local constancy on strata. -/
def constructibleCohomology :
    ObjectProperty (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))) :=
  DerivedCategory.cohomologyIn
    (Sheaf.IsConstructibleEtaleModule
      (fun {Y} f ↦ ((smallEtalePullback f).sheafPullback
        (ModuleCat.{v} Λ) X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (F : Sheaf Y.smallEtaleTopology (ModuleCat.{v} Λ)) ↦
        Sheaf.IsFiniteTypeLocallyConstantModule F))

variable {X Λ} {U : Scheme.{u}}
variable [Abelian (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]
variable (j : U ⟶ X) [AlgebraicGeometry.Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]

/-- Étale restriction preserves constructible cohomology of derived module sheaves. -/
theorem constructibleCohomology_restriction
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (hK : constructibleCohomology X Λ K) :
    constructibleCohomology U Λ
      ((etaleRestrictionSheaf j (ModuleCat.{v} Λ)).mapDerivedCategory.obj K) := sorry

/-- Extension by zero along a quasi-compact and quasi-separated étale morphism
preserves constructible cohomology of derived module sheaves. -/
theorem constructibleCohomology_extensionByZero
    [QuasiCompact j] [QuasiSeparated j]
    (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ)))
    (hM : constructibleCohomology U Λ M) :
    constructibleCohomology X Λ
      ((moduleExtensionByZero (Λ := Λ) j).mapDerivedCategory.obj M) := sorry

end AlgebraicGeometry.Scheme.Etale.Derived
