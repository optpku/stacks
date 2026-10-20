module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport.Constructible
import StacksCheckRecall

/-!
# Constructible cohomology of compact-support pushforward of a locally constant sheaf

If `Y` is Noetherian affine of finite dimension, `Λ` is a Noetherian torsion ring,
and `F` is a finite-type locally constant étale sheaf of `Λ`-modules on an open
of the relative affine line `𝔸(ULift (Fin 1); Y)`, then `Rf_! F` has
constructible cohomology.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} {U : Scheme.{u}}
variable (i : U ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion i]
variable [IsAffine Y] [IsNoetherian Y]
variable [IsSeparated (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)]
variable [Scheme.Hom.FiniteType (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (F : Sheaf U.smallEtaleTopology (ModuleCat.{u} Λ))
variable (P : Compactification.Of Y (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)))
variable [HasSheafify (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etale,
  HasWeakSheafify ((Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology.over V)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G : (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]

variable [Sheaf.IsFiniteTypeLocallyConstantModule F]

/- Lemma 63.14.3: if `Y` is a Noetherian affine scheme of finite dimension,
`Λ` is a Noetherian torsion ring, `i : U ⟶ 𝔸(ULift (Fin 1); Y)` is an open
immersion, and `F` is a finite-type locally constant étale sheaf of `Λ`-modules
on `U`, then `Rf_! F` has constructible cohomology sheaves, where `f` is the
structure morphism `i ≫ 𝔸(ULift (Fin 1); Y) ↘ Y`. -/
@[stacks 0GKY] #check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.OpenAffineLine.cohomology_isConstructible i F P :
  AddMonoid.IsTorsion Λ → topologicalKrullDim Y < ⊤ →
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) (Λ := Λ) P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
              (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)))

/- Each integer-degree homology sheaf is constructible. -/
#check (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.OpenAffineLine.homology_isConstructible i F P :
  AddMonoid.IsTorsion Λ → topologicalKrullDim Y < ⊤ → ∀ n : ℤ,
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) (Λ := Λ) P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf (Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
                (ModuleCat.{u} Λ)) (0 : ℤ)).obj F))))

end AlgebraicGeometry.Scheme.Etale

end
