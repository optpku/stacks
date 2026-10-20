module

public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_11_7_Comparison
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartesian base change of derived étale upper shriek
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Etale
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h_cart : IsPullback g' f' f g)
  [IsSeparated f] [Scheme.Hom.FiniteType f]
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  (P : Of Y (Over.mk f))
  (Λ : Type u) [CommRing Λ]

  [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).Etale,
  HasWeakSheafify
    ((etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
    (ModuleCat.{u} Λ))]

  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  AddCommGrpCat.{u}]

  [HasSheafCompose X.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose X'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose P.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [P.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P ≫
      P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P ≫
      etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F]

  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]

  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op]

  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (etaleDerivedLowerShriek.interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ))]

  [((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    P.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback P.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      P.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (up ℤ))]
  [((smallEtalePullback
      (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (etaleDerivedLowerShriek.ambient f g f' g' h_cart P).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (up ℤ))]

  [(etaleModulePushforward P.obj.right.hom Λ ⋙
    etaleModuleSheafPullback g Λ).Additive]
  [(etaleModuleSheafPullback
      (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P) Λ ⋙
    etaleModulePushforward
      (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward
      (etaleDerivedLowerShriek.ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward P.obj.right.hom Λ).Additive]

  [((smallEtalePullback g).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology Y'.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback g).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology Y'.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
  [((smallEtalePullback g').sheafPushforwardContinuous
    (ModuleCat.{u} Λ) X.smallEtaleTopology X'.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback g').sheafPushforwardContinuous
      (ModuleCat.{u} Λ) X.smallEtaleTopology X'.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)) (up ℤ))]
  [IsGrothendieckAbelian (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [IsGrothendieckAbelian (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [((etaleDerivedLowerShriek (Over.mk f) P :
      EtaleDerived (Over.mk f).left Λ ⥤ EtaleDerived Y Λ)).IsLeftAdjoint]
  [((etaleDerivedLowerShriek (Over.mk f')
      (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P) :
      EtaleDerived (Over.mk f').left Λ ⥤ EtaleDerived Y' Λ)).IsLeftAdjoint]

namespace etaleDerivedUpperShriek

/-- Lemma 63.11.7: Consider a cartesian square of quasi-compact and
quasi-separated schemes with `f` separated and of finite type, and let `Λ` be
a torsion coefficient ring. Then
`Rf^! ∘ Rg_* = etaleDerivedPushforward g ⋙ etaleDerivedUpperShriek (Over.mk f) Λ P`
agrees with
`Rg'_* ∘ R(f')^! = etaleDerivedUpperShriek (Over.mk f') Λ P' ⋙ etaleDerivedPushforward g'`,
where `P'` is the base-changed compactification of `f'`. The identification is
the uniqueness-of-adjoints conjugate of `g⁻¹ ∘ Rf_! ≅ Rf'_! ∘ (g')⁻¹` from
Lemma 63.9.4. -/
@[stacks 0GLE]
def baseChangeIso (hΛ : AddMonoid.IsTorsion Λ) :
    etaleDerivedPushforward g ⋙ etaleDerivedUpperShriek (Over.mk f) Λ P ≅
      etaleDerivedUpperShriek (Over.mk f') Λ
          (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P) ⋙
        etaleDerivedPushforward g' :=
  baseChangeComparisonIso f g f' g' h_cart P Λ hΛ

/-- Evaluating the cartesian comparison for `Rf^!` on an object of
`D(Y'_étale, Λ)`. -/
def baseChange_app
    (hΛ : AddMonoid.IsTorsion Λ) (K : EtaleDerived Y' Λ) :
    (etaleDerivedUpperShriek (Over.mk f) Λ P).obj
        ((etaleDerivedPushforward g).obj K) ≅
      (etaleDerivedPushforward g').obj
        ((etaleDerivedUpperShriek (Over.mk f') Λ
            (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P)).obj
          K) :=
  (baseChangeIso f g f' g' h_cart P Λ hΛ).app K

/-- The labeled cartesian comparison for `Rf^!` is the conjugate comparison
constructed from `etaleDerivedLowerShriek.baseChangeIso`. -/
theorem baseChange_spec
    (hΛ : AddMonoid.IsTorsion Λ) :
    baseChangeIso f g f' g' h_cart P Λ hΛ =
      baseChangeComparisonIso f g f' g' h_cart P Λ hΛ :=
  sorry

end etaleDerivedUpperShriek

end AlgebraicGeometry.Scheme.Etale

end
