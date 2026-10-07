module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Constructible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v r

namespace AlgebraicGeometry.Scheme

variable {U X : Scheme.{u}} {Λ : Type v} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{v} Λ)]
variable [∀ (Y : Scheme.{u}) (V : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{v} Λ)]
variable [∀ (Y Z : Scheme.{u}) (f : Y ⟶ Z) (F : Z.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ),
  (smallEtalePullback f).op.HasLeftKanExtension F]
variable [Abelian (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [Abelian (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))]
variable [HasDerivedCategory.{r} (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))]

/- Lemma 59.76.2 (1): étale restriction preserves membership in D_c. -/
@[stacks 095X] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.constructibleCohomology_restriction :
    ∀ (j : U ⟶ X) [Etale j]
      [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
        (etaleRestriction j).op.HasLeftKanExtension F]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))),
      Etale.Derived.constructibleCohomology X Λ K →
        Etale.Derived.constructibleCohomology U Λ
          ((etaleRestrictionSheaf j (ModuleCat.{v} Λ)).mapDerivedCategory.obj K))

/- Lemma 59.76.2 (2): quasi-compact quasi-separated étale extension by zero
preserves membership in D_c. -/
@[stacks 095X] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.constructibleCohomology_extensionByZero :
    ∀ (j : U ⟶ X) [Etale j]
      [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
        (etaleRestriction j).op.HasLeftKanExtension F]
      [QuasiCompact j] [QuasiSeparated j]
      (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))),
      Etale.Derived.constructibleCohomology U Λ M →
        Etale.Derived.constructibleCohomology X Λ
          ((moduleExtensionByZero (Λ := Λ) j).mapDerivedCategory.obj M))

end AlgebraicGeometry.Scheme
