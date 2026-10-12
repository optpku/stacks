/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Monoidal

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

universe u w

variable {X : Scheme.{u}}

section Modules

variable {Λ : Type w} [CommRing Λ] [IsNoetherianRing Λ]
variable [∀ Y : Scheme.{u}, HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (U : Y.Etale),
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable [∀ (Y : Scheme.{u}) (f : Y ⟶ X) (P : X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ),
  (Scheme.smallEtalePullback f).op.HasLeftKanExtension P]
variable [((X.smallEtaleTopology.W :
  MorphismProperty (X.Etaleᵒᵖ ⥤ ModuleCat.{w} Λ))).IsMonoidal]

/-- The tensor product of constructible étale sheaves of finite-type `Λ`-modules is constructible.
-/
theorem CategoryTheory.Sheaf.IsConstructibleEtaleModule.tensor
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)}
    (hF : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) F)
    (hG : IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) G) :
    IsConstructibleEtaleModule
      (fun {Y} f ↦
        ((Scheme.smallEtalePullback f).sheafPullback (ModuleCat.{w} Λ)
          X.smallEtaleTopology Y.smallEtaleTopology).obj)
      (fun {Y} (G : Sheaf Y.smallEtaleTopology (ModuleCat.{w} Λ)) ↦
        IsFiniteTypeLocallyConstantModule G) (F ⊗ G) := sorry

end Modules
