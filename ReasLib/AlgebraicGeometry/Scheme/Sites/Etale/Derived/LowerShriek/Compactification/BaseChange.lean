/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import ReasLib.AlgebraicGeometry.Scheme.Compactification.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Transition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProperLowerShriek.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero.LowerShriek

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

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

-- Local instance justification (search instability): prefer the existing strong-to-weak projection for base topologies instead of repeatedly matching the section's over-site families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

-- Local declaration justification (definitional transport): compare the chosen source
-- localization with the identical source projected from the explicit over-object.
set_option backward.isDefEq.respectTransparency false

section Cartesian

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

  [HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [derivedX : HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [derivedY : HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [derivedXPrime : HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [derivedYPrime : HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : P.obj.right.left.Etale,
  HasWeakSheafify (P.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [derivedP : HasDerivedCategory
  (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient f g f' g' h_cart P).Etale,
  HasWeakSheafify ((ambient f g f' g' h_cart P).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [derivedPullbackP : HasDerivedCategory
  (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify P.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
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
  [HasSheafCompose (ambient f g f' g' h_cart P).smallEtaleTopology
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
  [(ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback P.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f g f' g' h_cart P ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource f g f' g' h_cart P ≫ P.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι P : X ⟶ P.obj.right.left)).op.HasLeftKanExtension F]
  [∀ F : (ambient f g f' g' h_cart P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift f g f' g' h_cart P ≫
      ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [kanComposite : ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F]

  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F]

  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ambientToSource f g f' g' h_cart P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι P : X ⟶ P.obj.right.left)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op]

  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P : X ⟶ P.obj.right.left)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P : X ⟶ P.obj.right.left)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P : X ⟶ P.obj.right.left)).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift f g f' g' h_cart P)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ))]

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
    (ComplexShape.up ℤ))]
  [((smallEtalePullback (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (ambient f g f' g' h_cart P).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (ambient f g f' g' h_cart P).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

  [(etaleModulePushforward P.obj.right.hom Λ ⋙
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ))).Additive]
  [((Sheaf.smallEtaleInverseImage (ambientToSource f g f' g' h_cart P) (ModuleCat.{u} Λ)) ⋙
    etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward (ambientToBase f g f' g' h_cart P) Λ).Additive]
  [(etaleModulePushforward P.obj.right.hom Λ).Additive]

/-- Sheafification of the base-changed ambient transfers from `ambient`. -/
instance instHasSheafify_compactificationPullback :
    HasSheafify
      (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) :=
  inferInstanceAs
    (HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))

/-- Weak sheafification of the base-changed ambient transfers from `ambient`. -/
instance instHasWeakSheafify_compactificationPullback :
    HasWeakSheafify
      (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) :=
  inferInstanceAs
    (HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
      (ModuleCat.{u} Λ))

/-- Derived categories of the base-changed ambient transfer from `ambient`. -/
instance instHasDerivedCategory_compactificationPullback
    [hDerived : HasDerivedCategory.{v}
      (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasDerivedCategory.{v}
      (Sheaf (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) := hDerived

/-- Over-objects of étale sheaves on the base-changed ambient transfer from
`ambient`. -/
instance instHasWeakSheafify_compactificationPullback_over
    (U : (compactificationPullback f g f' g' h_cart P).obj.right.left.Etale) :
    HasWeakSheafify
      ((compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) :=
  inferInstanceAs
    (HasWeakSheafify
      ((ambient f g f' g' h_cart P).smallEtaleTopology.over
        (U : (ambient f g f' g' h_cart P).Etale))
      (ModuleCat.{u} Λ))

/-- Restriction along the interior of the base-changed compactification
transfers from `interiorLift`. -/
instance instHasLeftKanExtension_etaleRestriction_compactificationPullback_ι :
    ∀ F : (Over.mk f').left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction
        (Of.ι (compactificationPullback f g f' g' h_cart P) :
        X' ⟶ (ambient f g f' g' h_cart P))).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension
      (F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ))

/-- Abelian restriction along the interior of the base-changed compactification. -/
instance instHasLeftKanExtension_etaleRestriction_compactificationPullback_ι_ab :
    ∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction
        (Of.ι (compactificationPullback f g f' g' h_cart P) :
        X' ⟶ (ambient f g f' g' h_cart P))).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F)

/-- Forgetting coefficients preserves left Kan extensions along the interior of
the base-changed compactification. -/
instance instPreservesLeftKanExtensions_pullbackInterior :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
        (Of.ι (compactificationPullback f g f' g' h_cart P) :
        X' ⟶ (ambient f g f' g' h_cart P))).op :=
  inferInstanceAs
    ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (interiorLift f g f' g' h_cart P)).op)

/-- Extension by zero along the interior of the base-changed compactification is
additive. -/
instance instAdditive_etaleExtensionByZero_compactificationPullback_ι :
    (etaleExtensionByZero (U := X')
      (Of.ι (compactificationPullback f g f' g' h_cart P) :
        X' ⟶ (ambient f g f' g' h_cart P))
      (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs
    ((etaleExtensionByZero (interiorLift f g f' g' h_cart P)
        (ModuleCat.{u} Λ)).Additive)

/-- Extension by zero along the interior of the base-changed compactification
preserves finite limits. -/
instance instPreservesFiniteLimits_pullbackExtension :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (Of.ι (compactificationPullback f g f' g' h_cart P) :
        X' ⟶ (ambient f g f' g' h_cart P)) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ)))

/-- Extension by zero along the interior of the base-changed compactification
preserves finite colimits. -/
instance instPreservesFiniteColimits_pullbackExtension :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (Of.ι (compactificationPullback f g f' g' h_cart P) :
        X' ⟶ (ambient f g f' g' h_cart P)) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteColimits
      (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ)))

/-- Continuous small-étale pushforward along the structure map of the
base-changed compactification is additive. -/
instance (priority := 10000) instAdditive_sheafPushforward_compactificationPullback_hom :
    ((smallEtalePullback
        (compactificationPullback f g f' g' h_cart P).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology).Additive :=
  inferInstanceAs
    (((smallEtalePullback (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
        (ModuleCat.{u} Λ) Y'.smallEtaleTopology
        (ambient f g f' g' h_cart P).smallEtaleTopology).Additive)

/-- The structure map of the base-changed compactification is right-derivable. -/
instance (priority := 10000) instHasRightDerived_compactificationPullback_hom :
    HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback
            (compactificationPullback f g f' g' h_cart P).obj.right.hom).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y'.smallEtaleTopology
          (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
          (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (HasRightDerivedFunctor
      (RightDerived.Cochain.toDerived
        ((smallEtalePullback (ambientToBase f g f' g' h_cart P)).sheafPushforwardContinuous
          (ModuleCat.{u} Λ) Y'.smallEtaleTopology
          (ambient f g f' g' h_cart P).smallEtaleTopology))
      (HomologicalComplex.quasiIso
        (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))
        (ComplexShape.up ℤ)))

/-- Compactification model of `g⁻¹ ∘ Rf_!`. -/
irreducible_def baseChangeDomain :
    (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) := by
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f).left.smallEtaleTopology
      (ModuleCat.{u} Λ)) := inferInstanceAs
        (HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f).left.Etale, HasWeakSheafify ((Over.mk f).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f).left.Etale,
      HasWeakSheafify ((Over.mk f).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  exact etaleDerivedLowerShriek (Over.mk f) P ⋙
    etaleModuleDerivedInverseImage g Λ

/-- `Rf'_!` of the base-changed compactification, as `j'_! ⋙ R f̄'_*`. -/
def lowerShriekPullback :
    (DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  (etaleExtensionByZero (U := X')
      (Of.ι (compactificationPullback f g f' g' h_cart P) :
        X' ⟶ (ambient f g f' g' h_cart P))
      (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
    etaleDerivedPushforward (ambientToBase f g f' g' h_cart P)

/-- Unfolding `lowerShriekPullback` recovers extension by zero along `j'` and
derived pushforward along `f̄'`. -/
theorem lowerShriekPullback_eq :
    lowerShriekPullback f g f' g' h_cart P Λ =
      (etaleExtensionByZero (interiorLift f g f' g' h_cart P)
          (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :=
  sorry

/-- Compactification model of `Rf'_! ∘ (g')⁻¹`. -/
irreducible_def baseChangeCodomain :
    (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  etaleModuleDerivedInverseImage g' Λ ⋙
    lowerShriekPullback f g f' g' h_cart P Λ

/-- Interior compact-support mate `ḡ'⁻¹ ∘ j_! ⟶ j'_! ∘ (g')⁻¹`, transported
through the identification of extension by zero with `lowerShriekModule`. -/
def interiorMate :
    (etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙
        (etaleExtensionByZero (interiorLift f g f' g' h_cart P)
            (ModuleCat.{u} Λ)).mapDerivedCategory :=
  whiskerRight
      (extensionByZeroDerivedIsoLowerShriekModule (U := X) (Of.ι P) Λ).hom
      (etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ) ≫
    lowerShriekModuleDerivedBaseChange (X := X) (Of.ι P)
      (ambientToSource f g f' g' h_cart P)
      (interiorLift f g f' g' h_cart P) g'
      (interior_isPullback f g f' g' h_cart P) Λ ≫
    whiskerLeft (etaleModuleDerivedInverseImage g' Λ)
      (extensionByZeroDerivedIsoLowerShriekModule
          (interiorLift f g f' g' h_cart P) Λ).inv

/-- Proper base-change mate `g⁻¹ ∘ R f̄_* ⟶ R f̄'_* ∘ (ḡ')⁻¹` of the ambient
square of the compactification. -/
def properMate :
    (etaleDerivedPushforward P.obj.right.hom :
          (DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) ⋙
        etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ ⋙
        (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
          (DerivedCategory (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  etaleDerivedPushforwardBaseChange P.obj.right.hom g
    (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P)
    (ambient_isPullback f g f' g' h_cart P) Λ

/-- Unfolded comparison before transporting along the irreducible models. -/
def baseChangeUnfolded :
    ((etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward P.obj.right.hom :
          (DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))) ⋙
      etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙
        (etaleExtensionByZero (interiorLift f g f' g' h_cart P)
            (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
          (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
            (DerivedCategory (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  (Functor.associator
      (etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (etaleDerivedPushforward P.obj.right.hom :
        (DerivedCategory (Sheaf P.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))))
      (etaleModuleDerivedInverseImage g Λ)).hom ≫
    whiskerLeft
      (etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (properMate f g f' g' h_cart P Λ) ≫
    (Functor.associator
        (etaleExtensionByZero (U := X) (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
        (etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ)
        (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
          (DerivedCategory (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))))).inv ≫
    whiskerRight (interiorMate f g f' g' h_cart P Λ)
      (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
        (DerivedCategory (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))) ≫
    (Functor.associator
        (etaleModuleDerivedInverseImage g' Λ)
        (etaleExtensionByZero (interiorLift f g f' g' h_cart P)
            (ModuleCat.{u} Λ)).mapDerivedCategory
        (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
          (DerivedCategory (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))))).hom

/-- Canonical comparison `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of compactification
models, obtained by whiskering proper base change of `R f̄_*` with the
interior shriek mate. -/
@[irreducible]
def baseChange : baseChangeDomain f g P Λ ⟶
    baseChangeCodomain f g f' g' h_cart P Λ :=
  eqToHom (baseChangeDomain_def f g P Λ) ≫
    baseChangeUnfolded f g f' g' h_cart P Λ ≫
    eqToHom (baseChangeCodomain_def f g f' g' h_cart P Λ).symm

/-- Component of `baseChange` at an object of `D(X_étale, Λ)`. -/
@[irreducible]
def baseChange_app (K : (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))) :
    (baseChangeDomain f g P Λ).obj K ⟶
      (baseChangeCodomain f g f' g' h_cart P Λ).obj K :=
  (baseChange f g f' g' h_cart P Λ).app K

/-- The objectwise comparison is the component of `baseChange`. -/
theorem baseChange_app_eq (K : (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))) :
    (baseChange_app f g f' g' h_cart P Λ K :
      (baseChangeDomain f g P Λ).obj K ⟶
        (baseChangeCodomain f g f' g' h_cart P Λ).obj K) =
      (baseChange f g f' g' h_cart P Λ).app K := by
  unfold baseChange_app
  rfl

/-- Unfolding of `baseChange` as the whiskered proper and shriek mates. -/
theorem baseChange_eq :
    eqToHom (baseChangeDomain_def f g P Λ).symm ≫
        baseChange f g f' g' h_cart P Λ ≫
          eqToHom (baseChangeCodomain_def f g f' g' h_cart P Λ) =
      baseChangeUnfolded f g f' g' h_cart P Λ :=
  sorry

/-- The comparison `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` is an isomorphism on objects
of `D⁺_tors(X_étale, Λ)`. -/
theorem baseChange_isIso_of_isGE_isTorsion (K : (DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))))
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    IsIso (baseChange_app f g f' g' h_cart P Λ K) :=
  sorry

/-- If `Λ` is a torsion ring, the comparison `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` is
an isomorphism of functors on `D(X_étale, Λ)`. -/
theorem baseChange_isIso_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso (baseChange f g f' g' h_cart P Λ) :=
  sorry

/-- Torsion coefficients make the canonical base-change transformation invertible. -/
instance baseChange_isIso [hΛ : Fact (AddMonoid.IsTorsion Λ)] :
    IsIso (baseChange f g f' g' h_cart P Λ) :=
  baseChange_isIso_of_isTorsion f g f' g' h_cart P Λ hΛ.out

/-- Base change is invertible at each admissible complex. -/
instance baseChange_app_isIso (K : DerivedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
    [hK : Fact (Derived.compactSupportAdmissible X Λ K)] :
    IsIso ((baseChange f g f' g' h_cart P Λ).app K) := by
  rcases hK.out with ⟨ht, n, hn⟩ | hΛ
  · have comparison := baseChange_isIso_of_isGE_isTorsion f g f' g' h_cart P Λ K ht n
    exact (baseChange_app_eq f g f' g' h_cart P Λ K) ▸ comparison
  · exact ((@asIso _ _ _ _ (baseChange f g f' g' h_cart P Λ)
      (baseChange_isIso_of_isTorsion f g f' g' h_cart P Λ hΛ)).app K).isIso_hom

/-- The canonical comparison is invertible on the admissible source category. -/
instance baseChange_admissible_isIso :
    IsIso (whiskerLeft (Derived.compactSupportAdmissible X Λ).ι
      (baseChange f g f' g' h_cart P Λ)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K => ?_)
  exact baseChange_app_isIso f g f' g' h_cart P Λ K.obj (hK := ⟨K.property⟩)

/-- Base change gives a canonical isomorphism on admissible complexes. -/
def baseChangeAdmissibleIso :
    (Derived.compactSupportAdmissible X Λ).ι ⋙ baseChangeDomain f g P Λ ≅
      (Derived.compactSupportAdmissible X Λ).ι ⋙
        baseChangeCodomain f g f' g' h_cart P Λ :=
  asIso (whiskerLeft (Derived.compactSupportAdmissible X Λ).ι
    (baseChange f g f' g' h_cart P Λ))

/-- Torsion coefficients give the canonical base-change isomorphism. -/
def baseChangeIso (hΛ : AddMonoid.IsTorsion Λ) :
    baseChangeDomain f g P Λ ≅ baseChangeCodomain f g f' g' h_cart P Λ :=
  @asIso _ _ _ _ (baseChange f g f' g' h_cart P Λ)
    (baseChange_isIso_of_isTorsion f g f' g' h_cart P Λ hΛ)


variable (Q : Of Y (Over.mk f))
  [HasSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Q.obj.right.left.Etale,
  HasWeakSheafify (Q.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [derivedQ : HasDerivedCategory
  (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient f g f' g' h_cart Q).Etale,
  HasWeakSheafify ((ambient f g f' g' h_cart Q).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [derivedPullbackQ : HasDerivedCategory
  (Sheaf (ambient f g f' g' h_cart Q).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify Q.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose Q.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (ambient f g f' g' h_cart Q).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Q.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient f g f' g' h_cart Q).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback Q.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f g f' g' h_cart Q)).op.HasLeftKanExtension F]
  [∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToSource f g f' g' h_cart Q)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase f g f' g' h_cart Q ≫ g)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource f g f' g' h_cart Q ≫ Q.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι Q : X ⟶ Q.obj.right.left)).op.HasLeftKanExtension F]
  [∀ F : (ambient f g f' g' h_cart Q).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift f g f' g' h_cart Q)).op.HasLeftKanExtension F]
  [∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift f g f' g' h_cart Q ≫
      ambientToSource f g f' g' h_cart Q)).op.HasLeftKanExtension F]
  [∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ Of.ι Q)).op.HasLeftKanExtension F]
  [∀ F : Q.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ambientToSource f g f' g' h_cart Q)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ambientToSource f g f' g' h_cart Q)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι Q : X ⟶ Q.obj.right.left)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift f g f' g' h_cart Q)).op]
  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q : X ⟶ Q.obj.right.left)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι Q : X ⟶ Q.obj.right.left)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift f g f' g' h_cart Q)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift f g f' g' h_cart Q)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι Q : X ⟶ Q.obj.right.left)).op.HasLeftKanExtension F]
  [(etaleExtensionByZero (U := X) (Of.ι Q) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (U := X) (Of.ι Q) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (U := X) (Of.ι Q) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift f g f' g' h_cart Q)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (interiorLift f g f' g' h_cart Q) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (interiorLift f g f' g' h_cart Q) (ModuleCat.{u} Λ))]
  [((smallEtalePullback Q.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    Q.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback Q.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      Q.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf Q.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback (ambientToBase f g f' g' h_cart Q)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (ambient f g f' g' h_cart Q).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ambientToBase f g f' g' h_cart Q)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (ambient f g f' g' h_cart Q).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient f g f' g' h_cart Q).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleModulePushforward Q.obj.right.hom Λ ⋙
    (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ))).Additive]
  [((Sheaf.smallEtaleInverseImage (ambientToSource f g f' g' h_cart Q) (ModuleCat.{u} Λ)) ⋙
    etaleModulePushforward (ambientToBase f g f' g' h_cart Q) Λ).Additive]
  [(etaleModulePushforward (ambientToBase f g f' g' h_cart Q) Λ).Additive]
  [(etaleModulePushforward Q.obj.right.hom Λ).Additive]
  (φ : P ⟶ Q)

/-- Changing compactification transports the domain by the canonical transition. -/
def baseChange_domainTransition :
    baseChangeDomain f g Q Λ ⟶ baseChangeDomain f g P Λ := by
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f).left.smallEtaleTopology
      (ModuleCat.{u} Λ)) := inferInstanceAs
        (HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f).left.Etale, HasWeakSheafify ((Over.mk f).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f).left.Etale,
      HasWeakSheafify ((Over.mk f).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  exact eqToHom (baseChangeDomain_def f g Q Λ) ≫
    whiskerRight (@isoOfHom _ (Over.mk f) Λ _ (P) (Q) (φ)
      _ _ derivedX _ _ derivedP _ _ derivedQ derivedY
      _ _ (inferInstanceAs (HasSheafCompose X.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) (etaleModuleDerivedInverseImage g Λ) ≫
    eqToHom (baseChangeDomain_def f g P Λ).symm

-- Local declaration justification (elaboration complexity): reduce the two fixed pullback compactifications while explicitly supplying their existing transition data.
set_option maxHeartbeats 1500000 in
/-- Changing compactification transports the codomain by its base-changed transition. -/
def baseChange_codomainTransition :
    baseChangeCodomain f g f' g' h_cart Q Λ ⟶
      baseChangeCodomain f g f' g' h_cart P Λ := by
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology
      (ModuleCat.{u} Λ)) := inferInstanceAs
        (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f').left.Etale, HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f').left.Etale,
      HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory
      (Sheaf (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) := inferInstanceAs
      (HasDerivedCategory (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology
        (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient f g f' g' h_cart Q).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory
      (Sheaf (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) := inferInstanceAs
      (HasDerivedCategory (Sheaf (ambient f g f' g' h_cart Q).smallEtaleTopology
        (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify
      (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) := inferInstanceAs
    (HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology (AddCommGrpCat.{u})` at definitionally identical `HasSheafify (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology (AddCommGrpCat.{u})`; retain the supplied data under projection reduction.
  letI : HasSheafify
      (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
      (AddCommGrpCat.{u}) := inferInstanceAs
    (HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology (AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify
      (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) := inferInstanceAs
    (HasSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology (AddCommGrpCat.{u})` at definitionally identical `HasSheafify (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology (AddCommGrpCat.{u})`; retain the supplied data under projection reduction.
  letI : HasSheafify
      (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology
      (AddCommGrpCat.{u}) := inferInstanceAs
    (HasSheafify (ambient f g f' g' h_cart Q).smallEtaleTopology (AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Use supplied `(ambient f g f' g' h_cart P).smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})` at definitionally identical `(compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})`; retain the supplied data under projection reduction.
  letI : (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) := inferInstanceAs
    ((ambient f g f' g' h_cart P).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Use supplied `(ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})` at definitionally identical `(compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})`; retain the supplied data under projection reduction.
  letI : (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) := inferInstanceAs
    ((ambient f g f' g' h_cart P).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Use supplied `(ambient f g f' g' h_cart Q).smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})` at definitionally identical `(compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology.HasSheafCompose (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})`; retain the supplied data under projection reduction.
  letI : (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) := inferInstanceAs
    ((ambient f g f' g' h_cart Q).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Use supplied `(ambient f g f' g' h_cart Q).smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})` at definitionally identical `(compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})`; retain the supplied data under projection reduction.
  letI : (compactificationPullback f g f' g' h_cart Q).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) := inferInstanceAs
    ((ambient f g f' g' h_cart Q).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  rw [baseChangeCodomain_def, baseChangeCodomain_def]
  unfold lowerShriekPullback
  exact whiskerLeft (etaleModuleDerivedInverseImage g' Λ)
    (@isoOfHom _ (Over.mk f') Λ _ (compactificationPullback f g f' g' h_cart P) (compactificationPullback f g f' g' h_cart Q) (compactificationPullbackHom f g f' g' h_cart φ)
      _ _ derivedXPrime _ _ derivedPullbackP _ _ derivedPullbackQ derivedYPrime
      _ _ (inferInstanceAs (HasSheafCompose X'.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)

/-- Base change commutes with arbitrary compactification transitions on admissible complexes. -/
theorem baseChange_naturality :
    whiskerLeft (Derived.compactSupportAdmissible X Λ).ι
      (baseChange_domainTransition f g P Λ Q φ ≫
        baseChange f g f' g' h_cart P Λ) =
    whiskerLeft (Derived.compactSupportAdmissible X Λ).ι
      (baseChange f g f' g' h_cart Q Λ ≫
        baseChange_codomainTransition f g f' g' h_cart P Λ Q φ) := sorry

end Cartesian

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale
end
