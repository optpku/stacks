/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.InverseImage.Adjunction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.UpperShriek

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor
open CategoryTheory.GrothendieckTopology
open CategoryTheory.Sheaf
open CategoryTheory.Functor.RightDerived
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Compactification
open AlgebraicGeometry.Scheme.Etale
open ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

section Cartesian

-- Local declaration justification (definitional transport): the public mate
-- construction and its law use the two private transports of the actual
-- lower-shriek functors; default public elaboration hides these private names.
set_option backward.privateInPublic true

-- The over-objects are written in constructor form so that their source
-- projections reduce to the schemes carrying the supplied derived categories.

variable {X Y X' Y' : Scheme.{u}}
  (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (h_cart : IsPullback g' f' f g)
  [IsSeparated f] [Scheme.Hom.FiniteType f]
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  (P : Of Y (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y))
  (Λ : Type u) [CommRing Λ]
  [hΛ : Fact (AddMonoid.IsTorsion Λ)]

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
  [kanComposite : ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F]

  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' : X' ⟶ (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y).left)).op.HasLeftKanExtension F]
  [∀ F : (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (g' : X' ⟶ (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y).left)).op.HasLeftKanExtension F]

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
  [∀ F : (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
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
    Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)).Additive]
  [(Sheaf.smallEtaleInverseImage
      (etaleDerivedLowerShriek.ambientToSource f g f' g' h_cart P) (ModuleCat.{u} Λ) ⋙
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

namespace etaleDerivedLowerShriek

/-- Identification of `lowerShriekPullback` with the compactification
presentation `Rf'_!` of `compactificationPullback`. -/
private def lowerShriekPullbackIso :
    lowerShriekPullback f g f' g' h_cart P Λ ≅
      etaleDerivedLowerShriek (⟨X', ⟨⟨⟩⟩, f'⟩ : Over Y')
        (compactificationPullback f g f' g' h_cart P) :=
  eqToIso rfl

end etaleDerivedLowerShriek

namespace etaleDerivedUpperShriek

/-- The composite left adjoints `Rf'_! ∘ (g')⁻¹` and `g⁻¹ ∘ Rf_!` after
transporting `etaleDerivedLowerShriek.baseChangeIso` off its irreducible
compactification models. -/
private def baseChangeLeftIso :
    etaleModuleDerivedInverseImage g' Λ ⋙
        etaleDerivedLowerShriek (⟨X', ⟨⟨⟩⟩, f'⟩ : Over Y')
          (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P) ≅
      etaleDerivedLowerShriek (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y) P ⋙
        etaleModuleDerivedInverseImage g Λ :=
  (isoWhiskerLeft (etaleModuleDerivedInverseImage g' Λ)
      (etaleDerivedLowerShriek.lowerShriekPullbackIso f g f' g' h_cart P Λ)).symm ≪≫
    eqToIso (etaleDerivedLowerShriek.baseChangeCodomain_def f g f' g' h_cart P Λ).symm ≪≫
    (etaleDerivedLowerShriek.baseChangeIso f g f' g' h_cart P Λ hΛ.out
      (kanComposite := kanComposite)).symm ≪≫
    eqToIso (etaleDerivedLowerShriek.baseChangeDomain_def f g P Λ)

/-- The uniqueness-of-adjoints isomorphism
`Rg_* ⋙ Rf^! ≅ R(f')^! ⋙ Rg'_*` conjugate to lower-shriek base change. -/
def baseChangeIso :
    etaleDerivedPushforward g ⋙ etaleDerivedUpperShriek (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y) Λ P ≅
      etaleDerivedUpperShriek (⟨X', ⟨⟨⟩⟩, f'⟩ : Over Y') Λ
          (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P) ⋙
        etaleDerivedPushforward g' :=
  conjugateIsoEquiv
    ((etaleDerivedLowerShriekAdjunction (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y) Λ P).comp
      (etaleModuleDerivedInverseImageAdjunction g Λ))
    ((etaleModuleDerivedInverseImageAdjunction g' Λ).comp
      (etaleDerivedLowerShriekAdjunction (⟨X', ⟨⟨⟩⟩, f'⟩ : Over Y') Λ
        (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P)))
    (baseChangeLeftIso f g f' g' h_cart P Λ)

/-- Objectwise evaluation of `baseChangeIso`. -/
def baseChange_app
    (K : DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleDerivedUpperShriek (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y) Λ P).obj
        ((etaleDerivedPushforward g).obj K) ≅
      (etaleDerivedPushforward g').obj
        ((etaleDerivedUpperShriek (⟨X', ⟨⟨⟩⟩, f'⟩ : Over Y') Λ
            (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P)).obj
          K) :=
  (baseChangeIso f g f' g' h_cart P Λ).app K

/-- The comparison isomorphism is the conjugate of the transported inverse of
`etaleDerivedLowerShriek.baseChangeIso` along the composite adjunctions
`etaleDerivedLowerShriekAdjunction` then
`etaleModuleDerivedInverseImageAdjunction`. -/
theorem baseChange_spec :
    baseChangeIso f g f' g' h_cart P Λ =
      conjugateIsoEquiv
        ((etaleDerivedLowerShriekAdjunction (⟨X, ⟨⟨⟩⟩, f⟩ : Over Y) Λ P).comp
          (etaleModuleDerivedInverseImageAdjunction g Λ))
        ((etaleModuleDerivedInverseImageAdjunction g' Λ).comp
          (etaleDerivedLowerShriekAdjunction (⟨X', ⟨⟨⟩⟩, f'⟩ : Over Y') Λ
            (etaleDerivedLowerShriek.compactificationPullback f g f' g' h_cart P)))
        (baseChangeLeftIso f g f' g' h_cart P Λ) :=
  sorry

end etaleDerivedUpperShriek

end Cartesian

end AlgebraicGeometry.Scheme.Etale

end
