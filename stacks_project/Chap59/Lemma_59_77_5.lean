module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ConstructibleTorFinite.RestrictionExtension
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

/- Lemma 59.77.5 (1): étale restriction preserves `D_ctf` over a Noetherian ring. -/
@[stacks 0962] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.etaleRestriction_mem_constructibleTorFinite :
    ∀ (j : U ⟶ X) [AlgebraicGeometry.Etale j]
      [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
        (etaleRestriction j).op.HasLeftKanExtension F]
      (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{v} Λ))),
      Etale.Derived.constructibleTorFinite X Λ K →
        Etale.Derived.constructibleTorFinite U Λ
          ((etaleRestrictionSheaf j (ModuleCat.{v} Λ)).mapDerivedCategory.obj K))

/- Lemma 59.77.5 (2): quasi-compact quasi-separated étale extension by zero
preserves `D_ctf` over a Noetherian ring. -/
@[stacks 0962] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.moduleExtensionByZero_mem_constructibleTorFinite :
    ∀ (j : U ⟶ X) [AlgebraicGeometry.Etale j]
      [∀ F : U.Etaleᵒᵖ ⥤ ModuleCat.{v} Λ,
        (etaleRestriction j).op.HasLeftKanExtension F]
      [QuasiCompact j] [QuasiSeparated j]
      (M : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{v} Λ))),
      Etale.Derived.constructibleTorFinite U Λ M →
        Etale.Derived.constructibleTorFinite X Λ
          ((moduleExtensionByZero (Λ := Λ) j).mapDerivedCategory.obj M))

end AlgebraicGeometry.Scheme
