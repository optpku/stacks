/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible cohomology of compact-support pushforward of a constructible torsion sheaf

If `Y` is affine, `Λ` is a Noetherian ring, and `F` is a constructible torsion
étale sheaf of `Λ`-modules on the relative affine line
`𝔸(ULift (Fin 1); Y)`, then `Rf_! F` has constructible cohomology.
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

/-- The object of `Over Y` given by the relative affine line
`𝔸(ULift (Fin 1); Y)`. -/
abbrev affineLineOver (Y : Scheme.{u}) : Over Y :=
  Over.mk (𝔸(ULift.{u} (Fin 1); Y) ↘ Y)

/-- The structure morphism of `affineLineOver Y` is the relative affine line
over `Y`. -/
theorem affineLineOver_hom (Y : Scheme.{u}) :
    (affineLineOver Y).hom = 𝔸(ULift.{u} (Fin 1); Y) ↘ Y :=
  sorry

/-- The domain of `affineLineOver Y` is the relative affine line over `Y`. -/
theorem affineLineOver_left (Y : Scheme.{u}) :
    (affineLineOver Y).left = 𝔸(ULift.{u} (Fin 1); Y) :=
  sorry

variable {Y : Scheme.{u}}
variable [IsAffine Y]
variable [IsSeparated (affineLineOver Y).hom]
variable [Scheme.Hom.FiniteType (affineLineOver Y).hom]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (F : Sheaf (affineLineOver Y).left.smallEtaleTopology (ModuleCat.{u} Λ))
variable (P : Compactification.Of Y (affineLineOver Y))
variable [HasSheafify (affineLineOver Y).left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : (affineLineOver Y).left.Etale,
  HasWeakSheafify ((affineLineOver Y).left.smallEtaleTopology.over V)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (affineLineOver Y).left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : (Over.left (P.obj.right)).Etale,
  HasWeakSheafify ((Over.left (P.obj.right)).smallEtaleTopology.over V)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (Over.left (P.obj.right)).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G : (affineLineOver Y).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
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
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ (affineLineOver Y).left)
    (G : (affineLineOver Y).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]
variable [(affineLineOver Y).left.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

/-- Lemma 63.14.4: if `Y` is an affine scheme, `Λ` is a Noetherian ring, and
`F` is a constructible torsion sheaf of `Λ`-modules on
`𝔸(ULift (Fin 1); Y)`, then `Rf_! F` has constructible cohomology sheaves,
where `f` is the structure morphism `𝔸(ULift (Fin 1); Y) ↘ Y`. -/
@[stacks 0GKZ]
theorem etaleDerivedLowerShriek_constructible_affineLine_cohomology_isConstructible
    (hF_cons :
      Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            (affineLineOver Y).left.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (hF_tors :
      Sheaf.IsLocallyTorsion
        ((sheafCompose (affineLineOver Y).left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F)) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek (affineLineOver Y) P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (affineLineOver Y).left.smallEtaleTopology
              (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) :=
  sorry

/-- Each homology sheaf of `Rf_! F` is a constructible étale sheaf of
`Λ`-modules on `Y`. -/
theorem etaleDerivedLowerShriek_constructible_affineLine_homology_isConstructibleEtaleModule
    (hF_cons :
      Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            (affineLineOver Y).left.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G) F)
    (hF_tors :
      Sheaf.IsLocallyTorsion
        ((sheafCompose (affineLineOver Y).left.smallEtaleTopology
            (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})).obj F))
    (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek (affineLineOver Y) P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf (affineLineOver Y).left.smallEtaleTopology
                (ModuleCat.{u} Λ)) (0 : ℤ)).obj F))) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
