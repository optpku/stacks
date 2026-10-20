module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.ConstructibleAffineLine
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

universe u

/- Lemma 63.14.4. For an affine scheme and a Noetherian coefficient ring, the
compact-support derived pushforward of a constructible torsion étale module sheaf
along the relative affine-line projection has constructible cohomology sheaves. -/
@[stacks 0GKZ] #check
  (AlgebraicGeometry.Scheme.Etale.Derived.lowerShriek_affineLine_constructible :
    ∀ {Y : Scheme.{u}}
      [IsAffine Y]
      {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
      (F : Sheaf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ))
      (P : Compactification.Of Y (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)))
      [HasSheafify (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ)]
      [HasDerivedCategory
        (Sheaf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ))]
      [HasSheafify (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ)]
      [HasDerivedCategory
        (Sheaf (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ))]
      [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
      [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
      [∀ G : (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
        (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
      [(etaleExtensionByZero (Compactification.Of.ι P)
          (ModuleCat.{u} Λ)).Additive]
      [PreservesFiniteLimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
      [PreservesFiniteColimits
        (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
      [((smallEtalePullback (Over.hom (P.obj.right))).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y.smallEtaleTopology
          (Over.left (P.obj.right)).smallEtaleTopology).Additive]
      [HasRightDerivedFunctor
        (RightDerived.Cochain.toDerived
          ((smallEtalePullback (Over.hom (P.obj.right))).sheafPushforwardContinuous
            (ModuleCat.{u} Λ) Y.smallEtaleTopology
            (Over.left (P.obj.right)).smallEtaleTopology))
        (HomologicalComplex.quasiIso
          (Sheaf (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ))
          (ComplexShape.up ℤ))]
      [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
      [∀ (Z : Scheme.{u}) (V : Z.Etale),
        HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
      [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
        (smallEtalePullback g).op.HasLeftKanExtension G]
      [∀ (Z : Scheme.{u}) (g : Z ⟶ (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left)
          (G : (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
        (smallEtalePullback g).op.HasLeftKanExtension G]
      [(Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology.HasSheafCompose
        (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    (_hF_cons :
      Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (_hF_tors :
      Sheaf.IsLocallyTorsion
        ((sheafCompose (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)),
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek (Λ := Λ) (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
              (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)))
