/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.GroupTheory.Torsion
public import Mathlib.Topology.KrullDimension
public import stacks_project.Chap59.Definition_59_71_1
public import stacks_project.Chap63.Definition_63_12_1_LowerShriek
import Mathlib.Tactic.CrossRefAttribute

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

/-- The object of `Over Y` given by an open immersion into the relative affine
line `𝔸(ULift (Fin 1); Y)`. -/
abbrev openAffineLineOver {Y U : Scheme.{u}}
    (i : U ⟶ 𝔸(ULift.{u} (Fin 1); Y)) : Over Y :=
  Over.mk (i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y)

/-- The structure morphism of `openAffineLineOver i` is `i` followed by the
relative affine line. -/
theorem openAffineLineOver_hom {Y U : Scheme.{u}}
    (i : U ⟶ 𝔸(ULift.{u} (Fin 1); Y)) :
    (openAffineLineOver i).hom = i ≫ 𝔸(ULift.{u} (Fin 1); Y) ↘ Y :=
  sorry

/-- The domain of `openAffineLineOver i` is `U`. -/
theorem openAffineLineOver_left {Y U : Scheme.{u}}
    (i : U ⟶ 𝔸(ULift.{u} (Fin 1); Y)) :
    (openAffineLineOver i).left = U :=
  sorry

/-- The ambient scheme of a fixed-interior compactification. -/
abbrev compactificationAmbient {S : Scheme.{u}} {X : Over S}
    (P : Compactification.Of S X) : Scheme.{u} :=
  Over.left (P.obj.right)

/-- The ambient scheme of `P` is the left object of `P.obj.right`. -/
theorem compactificationAmbient_eq {S : Scheme.{u}} {X : Over S}
    (P : Compactification.Of S X) :
    compactificationAmbient P = Over.left (P.obj.right) :=
  sorry

variable {Y : Scheme.{u}} {U : Scheme.{u}}
variable (i : U ⟶ 𝔸(ULift.{u} (Fin 1); Y)) [IsOpenImmersion i]
variable [IsAffine Y] [IsNoetherian Y]
variable [IsSeparated (openAffineLineOver i).hom]
variable [Scheme.Hom.FiniteType (openAffineLineOver i).hom]
variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
variable (F : Sheaf (openAffineLineOver i).left.smallEtaleTopology (ModuleCat.{u} Λ))
variable (P : Compactification.Of Y (openAffineLineOver i))
variable [HasSheafify (openAffineLineOver i).left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : (openAffineLineOver i).left.Etale,
  HasWeakSheafify ((openAffineLineOver i).left.smallEtaleTopology.over V)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (openAffineLineOver i).left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (compactificationAmbient P).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : (compactificationAmbient P).Etale,
  HasWeakSheafify ((compactificationAmbient P).smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (compactificationAmbient P).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ V : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ G : (openAffineLineOver i).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension G]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback (Over.hom (P.obj.right))).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (compactificationAmbient P).smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom (P.obj.right))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (compactificationAmbient P).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (compactificationAmbient P).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [∀ Z : Scheme.{u}, HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (V : Z.Etale),
  HasWeakSheafify (Z.smallEtaleTopology.over V) (ModuleCat.{u} Λ)]
variable [∀ (Z : Scheme.{u}) (g : Z ⟶ Y) (G : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ),
  (smallEtalePullback g).op.HasLeftKanExtension G]

/-- Lemma 63.14.3: if `Y` is a Noetherian affine scheme of finite dimension,
`Λ` is a Noetherian torsion ring, `i : U ⟶ 𝔸(ULift (Fin 1); Y)` is an open
immersion, and `F` is a finite-type locally constant étale sheaf of `Λ`-modules
on `U`, then `Rf_! F` has constructible cohomology sheaves, where `f` is the
structure morphism `i ≫ 𝔸(ULift (Fin 1); Y) ↘ Y`. -/
@[stacks 0GKY]
theorem etaleDerivedLowerShriek_locallyConstant_openAffineLine_cohomology_isConstructible
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim Y < ⊤) :
    DerivedCategory.cohomologyIn
      (Sheaf.IsConstructibleEtaleModule
        (fun {Z} g ↦
          ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
            Y.smallEtaleTopology Z.smallEtaleTopology).obj)
        (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G))
      ((etaleDerivedLowerShriek (openAffineLineOver i) P).obj
        ((DerivedCategory.singleFunctor
            (Sheaf (openAffineLineOver i).left.smallEtaleTopology
              (ModuleCat.{u} Λ)) (0 : ℤ)).obj F)) :=
  sorry

/-- Each homology sheaf of `Rf_! F` is a constructible étale sheaf of
`Λ`-modules on `Y`. -/
theorem etaleDerivedLowerShriek_locallyConstant_openAffineLine_homology_isConstructibleEtaleModule
    [Sheaf.IsFiniteTypeLocallyConstantModule F]
    (hΛ : AddMonoid.IsTorsion Λ) (hdim : topologicalKrullDim Y < ⊤) (n : ℤ) :
    Sheaf.IsConstructibleEtaleModule
      (fun {Z} g ↦
        ((smallEtalePullback g).sheafPullback (ModuleCat.{u} Λ)
          Y.smallEtaleTopology Z.smallEtaleTopology).obj)
      (fun {Z} G ↦ Sheaf.IsFiniteTypeLocallyConstantModule G)
      ((DerivedCategory.homologyFunctor
          (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) n).obj
        ((etaleDerivedLowerShriek (openAffineLineOver i) P).obj
          ((DerivedCategory.singleFunctor
              (Sheaf (openAffineLineOver i).left.smallEtaleTopology
                (ModuleCat.{u} Λ)) (0 : ℤ)).obj F))) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
