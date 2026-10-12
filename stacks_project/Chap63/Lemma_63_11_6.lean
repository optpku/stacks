/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Iso
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.«63_11_4_1_Trace»
public import stacks_project.Chap63.Definition_63_12_1_Gamma
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable (P : Compactification.Of Y X)
variable [HasSheafify (smallEtaleTopology X.left) (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify ((smallEtaleTopology X.left).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ)]
variable [∀ U : (Over.left P.obj.right).Etale,
  HasWeakSheafify ((smallEtaleTopology (Over.left P.obj.right)).over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))]
variable [HasSheafify (smallEtaleTopology Y) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify ((smallEtaleTopology Y).over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf (smallEtaleTopology Y) (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Compactification.Of.ι P)).op.HasLeftKanExtension F]
variable [(etaleExtensionByZero (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y)
    (smallEtaleTopology (Over.left P.obj.right))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (Over.hom P.obj.right)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y)
      (smallEtaleTopology (Over.left P.obj.right))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology (Over.left P.obj.right)) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback X.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback X.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) (smallEtaleTopology Y) (smallEtaleTopology X.left)))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [(etaleRestrictionSheaf (Compactification.Of.ι P)
    (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleRestrictionSheaf (Compactification.Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ).Additive]
variable [PreservesFiniteLimits
  (etaleModulePushforward (Compactification.Of.ι P) Λ)]
variable [PreservesFiniteColimits
  (etaleModulePushforward (Compactification.Of.ι P) Λ)]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ).PreservesInjectiveObjects]
variable [(ExactFunctor.of
    (etaleModulePushforward (Compactification.Of.ι P) Λ)).obj.PreservesInjectiveObjects]
variable [(etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
variable [(etaleModulePushforward X.hom Λ).Additive]
variable [(etaleModulePushforward
    (Compactification.Of.ι P ≫ Over.hom P.obj.right) Λ).Additive]
variable [(etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
    etaleModulePushforward (Over.hom P.obj.right) Λ).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (Compactification.Of.ι P) Λ ⋙
      etaleModulePushforward (Over.hom P.obj.right) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [MonoidalCategory (EtaleDerived X.left Λ)]
variable [MonoidalClosed (EtaleDerived X.left Λ)]
variable [MonoidalCategory (EtaleDerived (Over.left P.obj.right) Λ)]
variable [MonoidalClosed (EtaleDerived (Over.left P.obj.right) Λ)]
variable [MonoidalCategory (EtaleDerived Y Λ)]
variable [MonoidalClosed (EtaleDerived Y Λ)]
variable [(etaleDerivedExtensionByZero (Compactification.Of.ι P) Λ).OplaxMonoidal]
variable [(etaleDerivedExtensionByZeroAdjunction
    (Compactification.Of.ι P) Λ).ProjectionFormulaMap]
variable [(etaleDerivedPushforward (Over.hom P.obj.right) :
    EtaleDerived (Over.left P.obj.right) Λ ⥤ EtaleDerived Y Λ).LaxMonoidal]
variable [((etaleDerivedLowerShriek X P :
    EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]
variable [HasDerivedCategory (ModuleCat.{u} Λ)]
variable [((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale Y))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale Y))))
  (HomologicalComplex.quasiIso
    (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [((sheafSections X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
    (op (globalEtale X.left))).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((sheafSections X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
      (op (globalEtale X.left))))
  (HomologicalComplex.quasiIso
    (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward X.hom Λ ⋙
      (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (op (globalEtale Y))))
  (HomologicalComplex.quasiIso
    (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) (ComplexShape.up ℤ))]

/-- Pullback of `globalEtale Y` along `X.hom` is the identity étale object of
`X.left`, via `inv (pullback.snd (𝟙 Y) X.hom)` from
`pullback_snd_iso_of_left_iso`. -/
def etaleGlobalIdentityPullbackIso :
    (smallEtalePullback X.hom).obj (globalEtale Y) ≅ globalEtale X.left :=
  MorphismProperty.Over.isoMk
    { hom := Limits.pullback.snd (𝟙 Y) X.hom
      inv := (asIso (Limits.pullback.snd (𝟙 Y) X.hom)).inv
      hom_inv_id := sorry
      inv_hom_id := sorry }

/-- Underived Leray identification `Γ(X, -) ≅ Γ(Y, f_* -)`, by evaluating
sheaf sections along `etaleGlobalIdentityPullbackIso`. -/
def etaleModuleGlobalSectionsPushforwardIso :
    (sheafSections X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
        (op (globalEtale X.left)) ≅
      etaleModulePushforward X.hom Λ ⋙
        (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale Y)) :=
  NatIso.ofComponents
    (fun F ↦ F.obj.mapIso (Iso.op (etaleGlobalIdentityPullbackIso X))) sorry

/-- Cochain-level iterated unit comparing `R(Γ(Y) ∘ f_*)` with `Rf_* ⋙ RΓ(Y)`. -/
def etaleDerivedGammaPushforwardUnit :
    RightDerived.Cochain.toDerived
        (etaleModulePushforward X.hom Λ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (globalEtale Y))) ⟶
      (DerivedCategory.Q :
          CochainComplex (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ℤ ⥤
            EtaleDerived X.left Λ) ⋙
        (etaleDerivedPushforward X.hom ⋙ etaleDerivedGamma Y Λ) :=
  (Functor.isoWhiskerRight
        (mapHomologicalComplexCompIso
          (Iso.refl
            (etaleModulePushforward X.hom Λ ⋙
              (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
                (op (globalEtale Y))))
          (ComplexShape.up ℤ)).symm
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} Λ) ℤ ⥤
            DerivedCategory (ModuleCat.{u} Λ)) ≪≫
      Functor.associator _ _ _).hom ≫
    RightDerived.Composition.iteratedUnit
      (RightDerived.Cochain.unit (etaleModulePushforward X.hom Λ))
      (RightDerived.Cochain.unit
        ((sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale Y))))

/-- Derived Leray comparison `RΓ(X, -) ⟶ RΓ(Y, Rf_* -)`, obtained by transporting
the underived sections isomorphism along `RightDerived.natIsoOfIso` and the
cochain units, then comparing with the iterated unit of `Rf_* ⋙ RΓ(Y)`. -/
def etaleDerivedGammaPushforward :
    etaleDerivedGamma X.left Λ ⟶
      etaleDerivedPushforward X.hom ⋙ etaleDerivedGamma Y Λ :=
  (RightDerived.natIsoOfIso
      (DerivedCategory.Q :
        CochainComplex (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ)) ℤ ⥤
          EtaleDerived X.left Λ)
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))
      (RightDerived.Cochain.unit
        ((sheafSections X.left.smallEtaleTopology (ModuleCat.{u} Λ)).obj
          (op (globalEtale X.left))))
      (RightDerived.Cochain.unit
        (etaleModulePushforward X.hom Λ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (globalEtale Y))))
      (Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex
          (etaleModuleGlobalSectionsPushforwardIso X) (ComplexShape.up ℤ))
        (DerivedCategory.Q :
          CochainComplex (ModuleCat.{u} Λ) ℤ ⥤
            DerivedCategory (ModuleCat.{u} Λ)))).hom ≫
    (RightDerived.Cochain.functor
        (etaleModulePushforward X.hom Λ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (globalEtale Y)))).rightDerivedDesc
      (RightDerived.Cochain.unit
        (etaleModulePushforward X.hom Λ ⋙
          (sheafSections Y.smallEtaleTopology (ModuleCat.{u} Λ)).obj
            (op (globalEtale Y))))
      (HomologicalComplex.quasiIso
        (Sheaf (smallEtaleTopology X.left) (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ))
      (etaleDerivedPushforward X.hom ⋙ etaleDerivedGamma Y Λ)
      (etaleDerivedGammaPushforwardUnit X)

/-- The morphism of global derived Homs induced by map (63.11.4.1): the Leray
comparison `RΓ(X, RHom_Λ(L, Rf^! K)) ⟶ RΓ(Y, Rf_* RHom_Λ(L, Rf^! K))`,
followed by `etaleDerivedGamma Y Λ` applied to `etaleDerivedSheafyTrace`. -/
def etaleDerivedGlobalTrace
    (L : EtaleDerived X.left Λ) (K : EtaleDerived Y Λ) :
    (etaleDerivedGamma X.left Λ).obj
        ((ihom L).obj ((etaleDerivedUpperShriek X Λ P).obj K)) ⟶
      (etaleDerivedGamma Y Λ).obj
        ((ihom ((etaleDerivedLowerShriek X P).obj L)).obj K) :=
  (etaleDerivedGammaPushforward X).app
      ((ihom L).obj ((etaleDerivedUpperShriek X Λ P).obj K)) ≫
    (etaleDerivedGamma Y Λ).map (etaleDerivedSheafyTrace X P L K)

/-- Lemma 63.11.6: for a separated finite-type morphism `X.hom : X.left ⟶ Y`
of quasi-compact quasi-separated schemes and a torsion ring `Λ`, the
sheafy-trace morphism of (63.11.4.1) induces an isomorphism
`RHom_X(L, Rf^! K) ⟶ RHom_Y(Rf_! L, K)` of global derived homs for every
`K` in `D(Y_étale, Λ)` and `L` in `D(X_étale, Λ)`. Global derived Hom is
`RΓ` of internal Hom, so the induced map is the Leray comparison
`RΓ(X, RHom_Λ(L, Rf^! K)) ⟶ RΓ(Y, Rf_* RHom_Λ(L, Rf^! K))` followed by
`etaleDerivedGamma Y Λ` applied to `etaleDerivedSheafyTrace`. -/
@[stacks 0GLD]
theorem etaleDerivedGlobalTrace_isIso
    (hΛ : AddMonoid.IsTorsion Λ) (L : EtaleDerived X.left Λ)
    (K : EtaleDerived Y Λ) :
    IsIso (etaleDerivedGlobalTrace X P L K) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
