module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Constructible
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.CompactSupport
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.Derived

variable {Y : Scheme.{u}}
variable [hAffine : IsAffine Y]
variable {Λ : Type u} [CommRing Λ] [hNoetherian : IsNoetherianRing Λ]
variable (F : Sheaf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ))
variable (P : Compactification.Of Y (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)))
variable [HasSheafify (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G : (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback (Over.hom (P.obj.right))).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (Over.left (P.obj.right)).smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom (P.obj.right))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (Over.left (P.obj.right)).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left)
    (G : (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [(Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

include hAffine hNoetherian

/-- For an affine scheme and a commutative Noetherian coefficient ring, derived lower
shriek along the relative affine-line projection sends a constructible torsion étale
module sheaf placed in degree zero to an object with constructible cohomology. -/
theorem lowerShriek_affineLine_constructible
    (hF_cons :
      Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (hF_tors :
      Sheaf.IsLocallyTorsion
        ((sheafCompose (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek (Λ := Λ) (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
              (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) :=
  sorry

/-- Each integer-degree homology sheaf of the derived lower shriek of a constructible
torsion étale module sheaf along the affine-line projection over an affine scheme is
constructible over a commutative Noetherian coefficient ring. -/
theorem lowerShriek_affineLine_homology_constructible
    (hF_cons :
      Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (hF_tors :
      Sheaf.IsLocallyTorsion
        ((sheafCompose (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F))
    (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {_} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek (Λ := Λ) (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)) P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf (Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)).left.smallEtaleTopology
                (ModuleCat.{u} Λ)) (0 : ℤ)).obj F))) :=
  lowerShriek_affineLine_constructible F P hF_cons hF_tors n

end AlgebraicGeometry.Scheme.Etale.Derived

end
