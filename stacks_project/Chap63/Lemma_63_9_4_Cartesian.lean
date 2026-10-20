module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.GroupTheory.Torsion
public import stacks_project.Chap63.Lemma_63_8_5_Comparison
public import stacks_project.Chap63.Lemma_63_9_2_Comparison
public import stacks_project.Chap63.Lemma_63_9_4_Pullback

/-!
# Derived étale lower shriek base change

Canonical comparison `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` of compactification
models attached to a cartesian square, assembled from proper base change of
`R f̄_*` and compact-support base change of `j_!`.
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

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale
namespace etaleDerivedLowerShriek

-- Local instance justification (search instability): prefer the existing strong-to-weak projection for base topologies instead of repeatedly matching the section's over-site families.
attribute [local instance 10000] HasSheafify.isRightAdjoint

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
  [HasSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ambient f g f' g' h_cart P).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient f g f' g' h_cart P).Etale,
  HasWeakSheafify ((ambient f g f' g' h_cart P).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
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
  (smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : (ambient f g f' g' h_cart P).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift f g f' g' h_cart P ≫
      ambientToSource f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
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
  (etaleRestriction (Of.ι P)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op]

  [∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι P)).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ))]
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
    etaleModuleSheafPullback g Λ).Additive]
  [(etaleModuleSheafPullback (ambientToSource f g f' g' h_cart P) Λ ⋙
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
instance instHasDerivedCategory_compactificationPullback :
    HasDerivedCategory
      (Sheaf (compactificationPullback f g f' g' h_cart P).obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (HasDerivedCategory
      (Sheaf (ambient f g f' g' h_cart P).smallEtaleTopology (ModuleCat.{u} Λ)))

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
        (Of.ι (compactificationPullback f g f' g' h_cart P))).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension
      (F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ))

/-- Restriction along the interior of the base-changed compactification, as a
morphism out of `X'`. -/
instance instHasLeftKanExtension_pullbackInterior_source :
    ∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction
        (Of.ι (compactificationPullback f g f' g' h_cart P))).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F)

/-- Abelian restriction along the interior of the base-changed compactification. -/
instance instHasLeftKanExtension_etaleRestriction_compactificationPullback_ι_ab :
    ∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction
        (Of.ι (compactificationPullback f g f' g' h_cart P))).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((etaleRestriction (interiorLift f g f' g' h_cart P)).op.HasLeftKanExtension F)

/-- Forgetting coefficients preserves left Kan extensions along the interior of
the base-changed compactification. -/
instance instPreservesLeftKanExtensions_pullbackInterior :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction
        (Of.ι (compactificationPullback f g f' g' h_cart P))).op :=
  inferInstanceAs
    ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (interiorLift f g f' g' h_cart P)).op)

/-- Extension by zero along the interior of the base-changed compactification is
additive. -/
instance instAdditive_etaleExtensionByZero_compactificationPullback_ι :
    (etaleExtensionByZero
      (Of.ι (compactificationPullback f g f' g' h_cart P))
      (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs
    ((etaleExtensionByZero (interiorLift f g f' g' h_cart P)
        (ModuleCat.{u} Λ)).Additive)

/-- Extension by zero along the interior of the base-changed compactification
preserves finite limits. -/
instance instPreservesFiniteLimits_pullbackExtension :
    PreservesFiniteLimits
      (etaleExtensionByZero
        (Of.ι (compactificationPullback f g f' g' h_cart P)) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteLimits
      (etaleExtensionByZero (interiorLift f g f' g' h_cart P) (ModuleCat.{u} Λ)))

/-- Extension by zero along the interior of the base-changed compactification
preserves finite colimits. -/
instance instPreservesFiniteColimits_pullbackExtension :
    PreservesFiniteColimits
      (etaleExtensionByZero
        (Of.ι (compactificationPullback f g f' g' h_cart P)) (ModuleCat.{u} Λ)) :=
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

/-- `Over.mk f` has the same underlying étale site as `X`. -/
instance instHasSheafCompose_overMk_f :
    HasSheafCompose (Over.mk f).left.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    (HasSheafCompose X.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- `Over.mk f'` has the same underlying étale site as `X'`. -/
instance instHasSheafCompose_overMk_f' :
    HasSheafCompose (Over.mk f').left.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
  inferInstanceAs
    (HasSheafCompose X'.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

/-- Left Kan extensions along `g'` transfer from `X` to `Over.mk f`. -/
instance instHasLeftKanExtension_overMk_g' :
    ∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback g').op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((smallEtalePullback g').op.HasLeftKanExtension
      (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ))

/-- Abelian left Kan extensions along `g'` transfer from `X` to `Over.mk f`. -/
instance instHasLeftKanExtension_overMk_g'_ab :
    ∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback g').op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((smallEtalePullback g').op.HasLeftKanExtension
      (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))

/-- Left Kan extensions along `g'` as a morphism into `(Over.mk f).left`. -/
instance instHasLeftKanExtension_overMk_g'_hom :
    ∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((smallEtalePullback g').op.HasLeftKanExtension
      (F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ))

/-- Abelian left Kan extensions along `g'` as a morphism into `(Over.mk f).left`. -/
instance instHasLeftKanExtension_overMk_g'_hom_ab :
    ∀ F : (Over.mk f).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((smallEtalePullback g').op.HasLeftKanExtension
      (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))

/-- Forgetting coefficients preserves left Kan extensions along `g'` into
`(Over.mk f).left`. -/
instance instPreservesLeftKanExtensions_overMk_g'_hom :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback (g' : X' ⟶ (Over.mk f).left)).op :=
  inferInstanceAs
    ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback g').op)

/-- Left Kan extensions along `(g' : X' ⟶ (Over.mk f).left) ≫ Of.ι P`. -/
instance instHasLeftKanExtension_overMk_g'_hom_comp_ι :
    ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback
        ((g' : X' ⟶ (Over.mk f).left) ≫ Of.ι P)).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F)

/-- Interior immersion of `P`, as a morphism out of `X`. -/
abbrev interiorι (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    X ⟶ P.obj.right.left :=
  Of.ι P

/-- `interiorι` is the compactification interior `Of.ι`. -/
theorem interiorι_eq (f : X ⟶ Y) (P : Of Y (Over.mk f)) :
    interiorι f P = Of.ι P :=
  sorry

/-- Left Kan extensions along `interiorι` transfer from `Of.ι`. -/
instance instHasLeftKanExtension_interiorι :
    ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (interiorι f P)).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((smallEtalePullback (Of.ι P)).op.HasLeftKanExtension F)

/-- The interior immersion `interiorι` is étale. -/
instance instEtale_interiorι : Etale (interiorι f P) :=
  inferInstanceAs (Etale (Of.ι P))

/-- The interior immersion `interiorι` is separated. -/
instance instIsSeparated_interiorι : IsSeparated (interiorι f P) :=
  inferInstanceAs (IsSeparated (Of.ι P))

/-- The interior immersion `interiorι` is locally quasi-finite. -/
instance instLocallyQuasiFinite_interiorι :
    LocallyQuasiFinite (interiorι f P) :=
  inferInstanceAs (LocallyQuasiFinite (Of.ι P))

/-- The interior immersion `interiorι` is locally of finite type. -/
instance instLocallyOfFiniteType_interiorι :
    LocallyOfFiniteType (interiorι f P) :=
  inferInstanceAs (LocallyOfFiniteType (Of.ι P))

/-- Left Kan extensions along `g' ≫ interiorι` transfer from `g' ≫ Of.ι`. -/
instance instHasLeftKanExtension_g'_comp_interiorι :
    ∀ F : P.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (g' ≫ interiorι f P)).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((smallEtalePullback (g' ≫ Of.ι P)).op.HasLeftKanExtension F)

/-- Restriction along `interiorι` transfers from `Of.ι`. -/
instance instHasLeftKanExtension_etaleRestriction_interiorι :
    ∀ F : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (interiorι f P)).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((etaleRestriction (Of.ι P)).op.HasLeftKanExtension F)

/-- Abelian restriction along `interiorι` transfers from `Of.ι`. -/
instance instHasLeftKanExtension_etaleRestriction_interiorι_ab :
    ∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (interiorι f P)).op.HasLeftKanExtension F :=
  fun F ↦ inferInstanceAs
    ((etaleRestriction (Of.ι P)).op.HasLeftKanExtension F)

/-- Forgetting coefficients preserves left Kan extensions along `interiorι`. -/
instance instPreservesLeftKanExtensions_etaleRestriction_interiorι :
    (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (interiorι f P)).op :=
  inferInstanceAs
    ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι P)).op)

/-- Extension by zero along `interiorι` is additive. -/
instance instAdditive_etaleExtensionByZero_interiorι :
    (etaleExtensionByZero (interiorι f P) (ModuleCat.{u} Λ)).Additive :=
  inferInstanceAs
    ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).Additive)

/-- Extension by zero along `interiorι` preserves finite limits. -/
instance instPreservesFiniteLimits_etaleExtensionByZero_interiorι :
    PreservesFiniteLimits
      (etaleExtensionByZero (interiorι f P) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteLimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)))

/-- Extension by zero along `interiorι` preserves finite colimits. -/
instance instPreservesFiniteColimits_etaleExtensionByZero_interiorι :
    PreservesFiniteColimits
      (etaleExtensionByZero (interiorι f P) (ModuleCat.{u} Λ)) :=
  inferInstanceAs
    (PreservesFiniteColimits (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)))

/-- Compactification model of `g⁻¹ ∘ Rf_!`. -/
irreducible_def baseChangeDomain :
    EtaleDerived X Λ ⥤ EtaleDerived Y' Λ :=
  etaleDerivedLowerShriek (Over.mk f) P ⋙
    etaleModuleDerivedInverseImage g Λ

/-- `Rf'_!` of the base-changed compactification, as `j'_! ⋙ R f̄'_*`. -/
def lowerShriekPullback :
    EtaleDerived X' Λ ⥤ EtaleDerived Y' Λ :=
  (etaleExtensionByZero
      (Of.ι (compactificationPullback f g f' g' h_cart P))
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
    EtaleDerived X Λ ⥤ EtaleDerived Y' Λ :=
  etaleModuleDerivedInverseImage g' Λ ⋙
    lowerShriekPullback f g f' g' h_cart P Λ

/-- Interior compact-support mate `ḡ'⁻¹ ∘ j_! ⟶ j'_! ∘ (g')⁻¹`, transported
through the identification of extension by zero with `lowerShriekModule`. -/
def interiorMate :
    (etaleExtensionByZero (interiorι f P) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙
        (etaleExtensionByZero (interiorLift f g f' g' h_cart P)
            (ModuleCat.{u} Λ)).mapDerivedCategory :=
  whiskerRight
      (extensionByZeroDerivedIsoLowerShriekModule (interiorι f P) Λ).hom
      (etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ) ≫
    lowerShriekModuleDerivedBaseChange (interiorι f P)
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
          EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Y Λ) ⋙
        etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ ⋙
        (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
          EtaleDerived (ambient f g f' g' h_cart P) Λ ⥤ EtaleDerived Y' Λ) :=
  etaleDerivedPushforwardBaseChange P.obj.right.hom g
    (ambientToBase f g f' g' h_cart P)
    (ambientToSource f g f' g' h_cart P)
    (ambient_isPullback f g f' g' h_cart P) Λ

/-- Unfolded comparison before transporting along the irreducible models. -/
def baseChangeUnfolded :
    ((etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward P.obj.right.hom :
          EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Y Λ)) ⋙
      etaleModuleDerivedInverseImage g Λ ⟶
      etaleModuleDerivedInverseImage g' Λ ⋙
        (etaleExtensionByZero (interiorLift f g f' g' h_cart P)
            (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
          (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
            EtaleDerived (ambient f g f' g' h_cart P) Λ ⥤ EtaleDerived Y' Λ) :=
  (Functor.associator
      (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (etaleDerivedPushforward P.obj.right.hom :
        EtaleDerived P.obj.right.left Λ ⥤ EtaleDerived Y Λ)
      (etaleModuleDerivedInverseImage g Λ)).hom ≫
    whiskerLeft
      (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
      (properMate f g f' g' h_cart P Λ) ≫
    (Functor.associator
        (etaleExtensionByZero (Of.ι P) (ModuleCat.{u} Λ)).mapDerivedCategory
        (etaleModuleDerivedInverseImage (ambientToSource f g f' g' h_cart P) Λ)
        (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
          EtaleDerived (ambient f g f' g' h_cart P) Λ ⥤ EtaleDerived Y' Λ)).inv ≫
    whiskerRight (interiorMate f g f' g' h_cart P Λ)
      (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
        EtaleDerived (ambient f g f' g' h_cart P) Λ ⥤ EtaleDerived Y' Λ) ≫
    (Functor.associator
        (etaleModuleDerivedInverseImage g' Λ)
        (etaleExtensionByZero (interiorLift f g f' g' h_cart P)
            (ModuleCat.{u} Λ)).mapDerivedCategory
        (etaleDerivedPushforward (ambientToBase f g f' g' h_cart P) :
          EtaleDerived (ambient f g f' g' h_cart P) Λ ⥤ EtaleDerived Y' Λ)).hom

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
def baseChange_app (K : EtaleDerived X Λ) :
    (baseChangeDomain f g P Λ).obj K ⟶
      (baseChangeCodomain f g f' g' h_cart P Λ).obj K :=
  (baseChange f g f' g' h_cart P Λ).app K

/-- The objectwise comparison is the component of `baseChange`. -/
theorem baseChange_app_eq (K : EtaleDerived X Λ) :
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
theorem baseChange_isIso_of_isGE_isTorsion (K : EtaleDerived X Λ)
    (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n] :
    IsIso (baseChange_app f g f' g' h_cart P Λ K) :=
  sorry

/-- If `Λ` is a torsion ring, the comparison `g⁻¹ ∘ Rf_! ⟶ Rf'_! ∘ (g')⁻¹` is
an isomorphism of functors on `D(X_étale, Λ)`. -/
theorem baseChange_isIso_of_isTorsion (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso (baseChange f g f' g' h_cart P Λ) :=
  sorry

/-- If `Λ` is a torsion ring, package `baseChange` as an isomorphism of
compactification models. -/
def baseChangeIso (hΛ : AddMonoid.IsTorsion Λ) :
    baseChangeDomain f g P Λ ≅
      baseChangeCodomain f g f' g' h_cart P Λ where
  hom := baseChange f g f' g' h_cart P Λ
  inv :=
    (@asIso _ _ _ _ (baseChange f g f' g' h_cart P Λ)
      (baseChange_isIso_of_isTorsion f g f' g' h_cart P Λ hΛ)).inv
  hom_inv_id := sorry
  inv_hom_id := sorry

end Cartesian

end etaleDerivedLowerShriek
end AlgebraicGeometry.Scheme.Etale
end
