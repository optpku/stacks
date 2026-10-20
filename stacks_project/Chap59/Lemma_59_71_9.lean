module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible.Tensor
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

universe u w

namespace CategoryTheory.Sheaf

variable {X : Scheme.{u}}

/- Lemma 59.71.9: for a scheme `X` and a Noetherian commutative ring `Λ`, the tensor product
of two constructible sheaves of `Λ`-modules on `Xₑₜ` is constructible. -/
@[stacks 095I] #check (CategoryTheory.Sheaf.IsConstructibleEtaleModule.tensor :
    {Λ : Type w} → [CommRing Λ] → [IsNoetherianRing Λ] →
    [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)] →
    [∀ (Y : Scheme.{u}) (U : Y.Etale),
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)] →
    [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
      (Scheme.smallEtalePullback f).op.HasLeftKanExtension P] →
    [((X.smallEtaleTopology.W :
      MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal] →
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)} →
    IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F →
    IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) G →
    IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) (F ⊗ G))

end CategoryTheory.Sheaf
