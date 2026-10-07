module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Constructible

@[expose] public section

open CategoryTheory

universe u v r

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable {U X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ V : X.Etale, Abelian (Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{v} Λ))]
variable [∀ V : U.Etale, Abelian (Sheaf (U.smallEtaleTopology.over V) (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [∀ V : X.Etale,
  HasDerivedCategory.{r} (Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{v} Λ))]
variable [∀ V : U.Etale,
  HasDerivedCategory.{r} (Sheaf (U.smallEtaleTopology.over V) (ModuleCat.{v} Λ))]
variable [∀ V : X.Etale, ((X.smallEtaleTopology.over V).W (A := ModuleCat.{v} Λ)).IsMonoidal]
variable [∀ V : U.Etale, ((U.smallEtaleTopology.over V).W (A := ModuleCat.{v} Λ)).IsMonoidal]
variable (j : U ⟶ X) [AlgebraicGeometry.Etale j]
variable [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
  (etaleRestriction j).op.HasLeftKanExtension F]

/-- Derived restriction along an étale morphism preserves constructible cohomology
and locally finite Tor dimension over a Noetherian coefficient ring. -/
theorem etaleRestriction_mem_constructibleTorFinite
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ)))
    (hK : constructibleTorFinite X Λ K) :
    constructibleTorFinite U Λ
      ((etaleRestrictionSheaf j (ModuleCat.{v} Λ)).mapDerivedCategory.obj K) := sorry

/-- Derived extension by zero along a quasi-compact quasi-separated étale morphism
preserves constructible cohomology and locally finite Tor dimension over a Noetherian
coefficient ring. -/
theorem moduleExtensionByZero_mem_constructibleTorFinite
    [QuasiCompact j] [QuasiSeparated j]
    (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ)))
    (hM : constructibleTorFinite U Λ M) :
    constructibleTorFinite X Λ
      ((moduleExtensionByZero (Λ := Λ) j).mapDerivedCategory.obj M) := sorry

end AlgebraicGeometry.Scheme.Etale.Derived
