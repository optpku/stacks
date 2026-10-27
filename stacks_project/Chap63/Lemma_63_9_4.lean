/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.BaseChange.Composition
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek


-- Local declaration justification (definitional transport): the typed checks use
-- the supplied localization data on the identical Over.mk scheme projections.
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
  (smallEtalePullback (Of.ι P : X ⟶ P.obj.right.left)).op.HasLeftKanExtension F]
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


variable (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ)))
  (h_tors : etaleDerivedIsTorsion K) (n : ℤ) [DerivedCategory.IsGE K n]

/- Lemma 63.9.4 (1): for a cartesian square of qcqs schemes with f separated
and of finite type, the canonical base-change map is invertible on bounded-below
complexes with torsion cohomology. -/
@[stacks 0F7L] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.baseChange_isIso_of_isGE_isTorsion
    f g f' g' h_cart P Λ K h_tors n :
    IsIso (baseChange_app f g f' g' h_cart P Λ K))

variable (hΛ : AddMonoid.IsTorsion Λ)

/- Lemma 63.9.4 (2): for torsion coefficients the canonical base-change map is
an isomorphism on the entire derived category. -/
@[stacks 0F7L] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.baseChange_isIso_of_isTorsion
    f g f' g' h_cart P Λ hΛ : IsIso (baseChange f g f' g' h_cart P Λ))

end Cartesian

section Composition

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g)
  {X' Y' Z' : Scheme.{u}}
  (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X.left)
  (h_upper : IsPullback c f' X.hom b) (h_lower : IsPullback b g' g a)
  [IsSeparated f'] [Scheme.Hom.FiniteType f']
  [IsSeparated g'] [Scheme.Hom.FiniteType g']
  [CompactSpace X'] [QuasiSeparatedSpace X']
  [CompactSpace Y'] [QuasiSeparatedSpace Y']
  [CompactSpace Z'] [QuasiSeparatedSpace Z']
  (Λ : Type u) [CommRing Λ]

  [IsOpenImmersion (Of.ι C.P_g)]
  [Etale (Of.ι C.P_g)]
  [IsSeparated (Of.ι C.P_g)]
  [LocallyQuasiFinite (Of.ι C.P_g)]
  [LocallyOfFiniteType (Of.ι C.P_g)]
  [IsSeparated (CompDiagram.openImmersion X g C)]
  [LocallyQuasiFinite (CompDiagram.openImmersion X g C)]
  [LocallyOfFiniteType (CompDiagram.openImmersion X g C)]
  [IsSeparated (Of.ι (CompDiagram.ofInterior X g C))]
  [LocallyQuasiFinite (Of.ι (CompDiagram.ofInterior X g C))]
  [LocallyOfFiniteType (Of.ι (CompDiagram.ofInterior X g C))]
  [IsSeparated (Of.ι (CompDiagram.ofComposite X g C))]
  [LocallyQuasiFinite
  (Of.ι (CompDiagram.ofComposite X g C))]
  [LocallyOfFiniteType
  (Of.ι (CompDiagram.ofComposite X g C))]

  [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify Z'.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : Z'.Etale,
  HasWeakSheafify (Z'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
  [HasDerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasWeakSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.interior X g C).Etale,
  HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : C.P_bar.obj.right.left.Etale,
  HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : C.P_g.obj.right.left.Etale,
  HasWeakSheafify (C.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose (CompDiagram.interior X g C).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose C.P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose C.P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior X g C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion X g C)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι C.P_g)).op]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback a).op.HasLeftKanExtension F]

  [(etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (CompDiagram.openImmersion X g C)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]

  [((smallEtalePullback (CompDiagram.toBase X g C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (CompDiagram.interior X g C).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toBase X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.interior X g C).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback C.P_bar.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
    C.P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C.P_bar.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) C.P_g.obj.right.left.smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback C.P_g.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology
    C.P_g.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback C.P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      C.P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback (CompDiagram.toComposite X g C)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z.smallEtaleTopology
    C.P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.toComposite X g C)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      C.P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

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
  [HasSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Z'.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose X'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Y'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose Z'.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Z'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback b).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback c).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback a).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback b).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback c).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback a).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback b).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback c).op]

  [(etaleModulePushforward (CompDiagram.toBase X g C) Λ).Additive]
  [(etaleModulePushforward C.P_bar.obj.right.hom Λ).Additive]
  [(etaleModulePushforward C.P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward (CompDiagram.toComposite X g C) Λ).Additive]
  [(etaleModulePushforward C.P_bar.obj.right.hom Λ ⋙
    etaleModulePushforward C.P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward (CompDiagram.toBase X g C) Λ ⋙
    lowerShriekModule (X := Y) (Of.ι C.P_g) Λ).Additive]
  [(lowerShriekModule (CompDiagram.openImmersion X g C) Λ ⋙
    etaleModulePushforward C.P_bar.obj.right.hom Λ).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward (CompDiagram.toBase X g C) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward C.P_bar.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived (etaleModulePushforward C.P_g.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.toComposite X g C) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward C.P_bar.obj.right.hom Λ ⋙
      etaleModulePushforward C.P_g.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.toBase X g C) Λ ⋙
      lowerShriekModule (X := Y) (Of.ι C.P_g) Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (lowerShriekModule (CompDiagram.openImmersion X g C) Λ ⋙
      etaleModulePushforward C.P_bar.obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]


variable [HasSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).Etale,
  HasWeakSheafify
    ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasSheafify
  (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)]
  [HasWeakSheafify
  (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (ambient g a g' b h_lower C.P_g).Etale,
  HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))]
  [HasSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).Etale,
  HasWeakSheafify
    ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    (etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleModulePushforward
    (CompDiagram.ofComposite X g C).obj.right.hom Λ).Additive]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (interiorLift g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (interiorLift g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [(CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient g a g' b h_lower C.P_g).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z.smallEtaleTopology
      (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
          (CompDiagram.ofComposite X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ambientToBase g a g' b h_lower C.P_g)).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (ambient g a g' b h_lower C.P_g).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleExtensionByZero
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (interiorLift g a g' b h_lower C.P_g)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (interiorLift g a g' b h_lower C.P_g) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (interiorLift g a g' b h_lower C.P_g) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (Of.ι (ofInteriorHom X g C)) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero (Of.ι (ofInteriorHom X g C)) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero (Of.ι (ofInteriorHom X g C)) (ModuleCat.{u} Λ))]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (interiorLift g a g' b h_lower C.P_g)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (ofInteriorHom X g C))).op]

  [HasSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
  [HasWeakSheafify Z.smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafCompose Z.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [Z.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose (ambient g a g' b h_lower C.P_g).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose
  (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasWeakSheafify
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose
  (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [((smallEtalePullback (ambientToBase g a g' b h_lower C.P_g)).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z'.smallEtaleTopology
    (ambient g a g' b h_lower C.P_g).smallEtaleTopology).Additive]
  [((smallEtalePullback
        (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology).Additive]
  [((smallEtalePullback
        (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
          (CompDiagram.ofComposite X g C))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)).smallEtaleTopology).Additive]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback C.P_g.obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToSource g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ambientToBase g a g' b h_lower C.P_g ≫ a)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource g a g' b h_lower C.P_g ≫ C.P_g.obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι C.P_g)).op.HasLeftKanExtension F]
  [∀ F : (ambient g a g' b h_lower C.P_g).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (interiorLift g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift g a g' b h_lower C.P_g ≫
      ambientToSource g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b ≫ Of.ι C.P_g)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk g).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (b : Y' ⟶ (Over.mk g).left)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (CompDiagram.toBase X g C)).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C) ≫ b)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C) ≫
      (ofInteriorHom X g C).obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C) ≫
      ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (c ≫ Of.ι (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (c : X' ⟶ (Over.mk X.hom).left)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (CompDiagram.ofComposite X g C).obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) ≫ a)).op.HasLeftKanExtension F]
  [∀ F : Z.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) ≫
      (CompDiagram.ofComposite X g C).obj.right.hom)).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C) ≫
      ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    ModuleCat.{u} Λ,
  (smallEtalePullback
    (c ≫ Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (c : X' ⟶ (Over.mk (X.hom ≫ g)).left)).op.HasLeftKanExtension F]
  [(etaleModulePushforward C.P_g.obj.right.hom Λ ⋙
    (Sheaf.smallEtaleInverseImage a (ModuleCat.{u} Λ))).Additive]
  [((Sheaf.smallEtaleInverseImage (ambientToSource g a g' b h_lower C.P_g) (ModuleCat.{u} Λ)) ⋙
    etaleModulePushforward (ambientToBase g a g' b h_lower C.P_g) Λ).Additive]
  [(etaleModulePushforward (ambientToBase g a g' b h_lower C.P_g) Λ).Additive]
  [(etaleModulePushforward (ofInteriorHom X g C).obj.right.hom Λ ⋙
    (Sheaf.smallEtaleInverseImage b (ModuleCat.{u} Λ))).Additive]
  [((Sheaf.smallEtaleInverseImage (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C)) (ModuleCat.{u} Λ)) ⋙
    etaleModulePushforward
      (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C)) Λ).Additive]
  [(etaleModulePushforward
    (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C)) Λ).Additive]
  [(etaleModulePushforward (CompDiagram.ofComposite X g C).obj.right.hom Λ ⋙
    (Sheaf.smallEtaleInverseImage a (ModuleCat.{u} Λ))).Additive]
  [((Sheaf.smallEtaleInverseImage (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)) (ModuleCat.{u} Λ)) ⋙
    etaleModulePushforward
      (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
        (CompDiagram.ofComposite X g C)) Λ).Additive]
  [(etaleModulePushforward
    (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C)) Λ).Additive]

  [∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ambientToSource g a g' b h_lower C.P_g)).op.HasLeftKanExtension F]
  [∀ F : (Over.mk g).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (b : Y' ⟶ (Over.mk g).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ambientToSource g a g' b h_lower C.P_g)).op]
  [∀ F : (ofInteriorHom X g C).obj.right.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk X.hom).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (c : X' ⟶ (Over.mk X.hom).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback
    (ambientToSource X.hom b f' c h_upper (ofInteriorHom X g C))).op]
  [∀ F : (CompDiagram.ofComposite X g C).obj.right.left.Etaleᵒᵖ ⥤
    AddCommGrpCat.{u},
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
  [∀ F : (Over.mk (X.hom ≫ g)).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (c : X' ⟶ (Over.mk (X.hom ≫ g)).left)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback
    (ambientToSource (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
      (CompDiagram.ofComposite X g C))).op]

  [HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (ofInteriorHom X g C).obj.right.left.Etale,
  HasWeakSheafify
    ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  
  [HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(ofInteriorHom X g C).obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [((smallEtalePullback (ofInteriorHom X g C).obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (ofInteriorHom X g C).obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (ofInteriorHom X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (ofInteriorHom X g C).obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [HasWeakSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale,
  HasWeakSheafify
    ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  
  [((smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y.smallEtaleTopology
    (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y.smallEtaleTopology
      (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]

variable [IsOpenImmersion
  (Of.ι (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower).P_g)]
  [Etale
  (Of.ι (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower).P_g)]
  [IsSeparated
  (Of.ι (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower).P_g)]
  [LocallyQuasiFinite
  (Of.ι (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower).P_g)]
  [LocallyOfFiniteType
  (Of.ι (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower).P_g)]
  [IsSeparated
  (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyQuasiFinite
  (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower))]
  [LocallyOfFiniteType
  (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower))]
  [IsSeparated
  (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)))]
  [LocallyQuasiFinite
  (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)))]
  [LocallyOfFiniteType
  (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)))]
  [IsSeparated
  (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)))]
  [LocallyQuasiFinite
  (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)))]
  [LocallyOfFiniteType
  (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)))]
  [HasSheafify
  (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)).Etale,
  HasWeakSheafify
    ((CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)).smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasSheafify
  (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.Etale,
  HasWeakSheafify
    ((CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  [HasDerivedCategory
  (Sheaf (CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
    (ModuleCat.{u} Λ))]
  [HasSheafify
  (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
  (ModuleCat.{u} Λ)]
  [∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
  HasWeakSheafify
    ((CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
  
  [HasSheafify
  (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology AddCommGrpCat.{u}]
  [HasSheafify
  (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafify
  (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
  AddCommGrpCat.{u}]
  [HasSheafCompose
  (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose
  (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [HasSheafCompose
  (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [(CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction
    (Of.ι (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower).P_g)).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))).op.HasLeftKanExtension F]
  [∀ F : (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
    h_upper h_lower)).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower))).op.HasLeftKanExtension F]
  [∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))).op.HasLeftKanExtension F]
  [∀ F : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction
    (Of.ι (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower).P_g)).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction
    (Of.ι (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower).P_g)).op]
  [(etaleExtensionByZero
    (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (Of.ι (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower).P_g)
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (Of.ι (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower).P_g)
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (Of.ι (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower).P_g)
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (CompDiagram.openImmersion (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower))
    (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
  (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))
    (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
  (etaleExtensionByZero
    (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)))
    (ModuleCat.{u} Λ))]
  [((smallEtalePullback
      (CompDiagram.toBase (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower))).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Y'.smallEtaleTopology
    (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)).smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toBase (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
          h_upper h_lower))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Y'.smallEtaleTopology
      (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower)).smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower)).smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ)
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology).Additive]
  [(
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) := inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))); HasRightDerivedFunctor (RightDerived.Cochain.toDerived ((smallEtalePullback (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.hom).sheafPushforwardContinuous (ModuleCat.{u} Λ) (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology)) (HomologicalComplex.quasiIso (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) (ComplexShape.up ℤ)))]
  [((smallEtalePullback
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.hom).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z'.smallEtaleTopology
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.hom).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.pullback X g C f' g' a b c
          h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [((smallEtalePullback
      (CompDiagram.toComposite (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower))).sheafPushforwardContinuous
    (ModuleCat.{u} Λ) Z'.smallEtaleTopology
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology).Additive]
  [HasRightDerivedFunctor
  (RightDerived.Cochain.toDerived
    ((smallEtalePullback
        (CompDiagram.toComposite (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
          h_upper h_lower))).sheafPushforwardContinuous
      (ModuleCat.{u} Λ) Z'.smallEtaleTopology
      (CompDiagram.pullback X g C f' g' a b c
        h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology))
  (HomologicalComplex.quasiIso
    (Sheaf (CompDiagram.pullback X g C f' g' a b c
          h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ))
    (ComplexShape.up ℤ))]
  [(etaleModulePushforward
    (CompDiagram.toBase (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)) Λ).Additive]
  [(etaleModulePushforward
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.hom Λ).Additive]
  [(etaleModulePushforward
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.hom Λ).Additive]
  [(etaleModulePushforward
    (CompDiagram.toComposite (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c
      h_upper h_lower)) Λ).Additive]


  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (ofInteriorHom X g C).obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (ofInteriorHom X g C).obj.right.hom).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (ofInteriorHom X g C).obj.right.hom).op]
  [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (CompDiagram.ofInterior X g C).obj.right.hom).op]
  [∀ F : Z.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).op.HasLeftKanExtension F]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (CompDiagram.ofComposite X g C).obj.right.hom).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (Of.ι C.P_g)).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (Of.ι (ofInteriorHom X g C))).op]
  [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback (Of.ι (CompDiagram.ofComposite X g C))).op]


/- Lemma 63.9.4 (3): the canonical base-change isomorphisms are compatible
with the composition isomorphisms on admissible complexes. -/
@[stacks 0F7L] #check
  (AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek.baseChange_comp
    X g C f' g' a b c h_upper h_lower Λ :
    whiskerLeft (Derived.compactSupportAdmissible X.left Λ).ι
      (baseChange_comp_outer X g C f' g' a b c h_upper h_lower Λ) =
    whiskerLeft (Derived.compactSupportAdmissible X.left Λ).ι
      (baseChange_comp_inner X g C f' g' a b c h_upper h_lower Λ))

end Composition
end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek
end
end
