module

public import stacks_project.Chap63.Lemma_63_9_1_Comparison

/-!
# Independence of derived étale lower shriek from the compactification

Lemma 63.9.1: for a finite type separated morphism of quasi-compact
quasi-separated schemes, the functors `Rf_!` constructed from a
compactification are, up to canonical isomorphism, independent of the choice
of compactification.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Compactification

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {Y : Scheme.{u}} (X : Over Y) {Λ : Type u} [CommRing Λ]
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable {P Q : Of Y X} (φ : P ⟶ Q)
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose Q.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Q.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι Q)).op]
variable [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
variable [(etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
variable [PreservesFiniteLimits (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
variable [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι Q) (ModuleCat.{u} Λ))]
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
variable [((smallEtalePullback Q.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    Q.obj.right.left.smallEtaleTopology).Additive]
variable [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback Q.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      Q.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
variable [((smallEtalePullback (Of.ambientMap φ)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Q.obj.right.left.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
variable [(etaleModulePushforward (Of.ambientMap φ) Λ).Additive]
variable [(etaleModulePushforward Q.obj.right.hom Λ).Additive]
variable [(etaleModulePushforward P.obj.right.hom Λ).Additive]

/-- Lemma 63.9.1 (1): Let `f : X ⟶ Y` be a finite type separated morphism of
quasi-compact and quasi-separated schemes. The functor
`Rf_! : D⁺_tors(X_étale, Λ) ⟶ D⁺_tors(Y_étale, Λ)` constructed from a
compactification is, up to canonical isomorphism, independent of the choice of
the compactification. -/
@[stacks 0F7I]
theorem etaleDerivedLowerShriek.isoOfHom_isIso_of_isGE_isTorsion
    (K : EtaleDerived X.left Λ) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    IsIso (etaleDerivedLowerShriek.isoOfHom_app X Λ φ K) :=
  sorry

/-- Lemma 63.9.1 (2): Let `f : X ⟶ Y` be a finite type separated morphism of
quasi-compact and quasi-separated schemes. If `Λ` is a torsion ring, then the
functor `Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` constructed from a
compactification is, up to canonical isomorphism, independent of the choice of
the compactification. -/
@[stacks 0F7I]
theorem etaleDerivedLowerShriek.isoOfHom_isIso_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso
      (etaleDerivedLowerShriek.isoOfHom X Λ φ :
        (etaleDerivedLowerShriek X Q :
            EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ) ⟶
          (etaleDerivedLowerShriek X P :
            EtaleDerived X.left Λ ⥤ EtaleDerived Y Λ)) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
