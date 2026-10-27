/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Transport
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.BaseChange

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.Scheme.Compactification

-- Local declaration justification (module visibility): the private computation
-- equalities are consumed only by the concrete constructions in this owner.
set_option backward.privateInPublic true

noncomputable section
universe u v

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
variable [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated g] [Scheme.Hom.FiniteType g]
variable [CompactSpace X.left] [QuasiSeparatedSpace X.left]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g) (Λ : Type u) [CommRing Λ]

/-- The alternate fixed-interior spelling uses the original interior sheafification. -/
def hasSheafify_ofInteriorHom
    [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)] :
    HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))

/-- Slice sheafification uses the same underlying site, without choosing a second instance. -/
def hasWeakSheafify_ofInteriorHom_over
    [∀ U : (CompDiagram.interior X g C).Etale,
      HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    (U : (ofInteriorHom X g C).obj.right.left.Etale) :
    HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) :=
  inferInstanceAs (HasWeakSheafify
    ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))

/-- The two spellings of the same interior use the same localization data and universe. -/
def hasDerivedCategory_ofInteriorHom
    [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : (CompDiagram.interior X g C).Etale,
      HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory.{v} (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasDerivedCategory.{v}
      (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  inferInstanceAs (HasDerivedCategory.{v}
    (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))

variable {X' Y' Z' : Scheme.{u}} (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
  (a : Z' ⟶ Z) (b : Y' ⟶ Y) (c : X' ⟶ X.left)
  (h_upper : IsPullback c f' X.hom b) (h_lower : IsPullback b g' g a)
variable [IsSeparated f'] [Scheme.Hom.FiniteType f']
variable [IsSeparated g'] [Scheme.Hom.FiniteType g']
variable [CompactSpace X'] [QuasiSeparatedSpace X']
variable [CompactSpace Y'] [QuasiSeparatedSpace Y']
variable [CompactSpace Z'] [QuasiSeparatedSpace Z']

-- Local declaration justification (module visibility): retain this implementation
-- equality privately while using its proof in the concrete public constructions.
set_option backward.privateInPublic true in
/-- The base compactification in the pulled-back diagram has the already chosen ambient. -/
private theorem stacked_P_g_ambient_eq :
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left =
      ambient g a g' b h_lower C.P_g := by
  rfl

/-- Reuse the lower ambient sheafification on the pulled-back base compactification. -/
def hasSheafify_stacked_P_g
    [HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)] :
    HasSheafify
      (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
      (ModuleCat.{u} Λ) := by
  rw [stacked_P_g_ambient_eq]
  infer_instance

/-- Reuse the lower ambient's slice sheafification on the same scheme. -/
def hasWeakSheafify_stacked_P_g_over
    [∀ U : (ambient g a g' b h_lower C.P_g).Etale,
      HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    (U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale) :
    HasWeakSheafify
      ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U)
      (ModuleCat.{u} Λ) := by
  revert U
  intro U
  exact inferInstanceAs (HasWeakSheafify
    ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))

/-- The pulled-back base compactification reuses the lower ambient's localization data. -/
def hasDerivedCategory_stacked_P_g
    [HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)]
    [∀ U : (ambient g a g' b h_lower C.P_g).Etale,
      HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory.{v}
      (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))] :
    HasDerivedCategory.{v}
      (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology
        (ModuleCat.{u} Λ)) := by
  rw [stacked_P_g_ambient_eq]
  infer_instance

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek
end

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

-- Local instance justification (search instability): Prefer HasSheafify.isRightAdjoint for the specified base sites; matching the simultaneous over-site HasWeakSheafify families instead leaves UnivLE constraints unsolved while elaborating the stacked context.
attribute [local instance 10000] HasSheafify.isRightAdjoint

-- Local declaration justification (definitional transport): match the supplied geometric and sheafification instances on the identical Over.mk scheme projections.
set_option backward.isDefEq.respectTransparency false


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
  [hasDerivedPushforwardBetweenAmbients : (
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

-- Local declaration justification (module visibility): retain this implementation
-- equality privately while using its proof in the concrete public constructions.
set_option backward.privateInPublic true in
omit hasDerivedPushforwardBetweenAmbients in
/-- The lower compactification is the identical constructed base model. -/
private theorem stacked_lowerModel_eq :
    -- Local instance justification (defeq pin): Use supplied `HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk g').left.Etale, HasWeakSheafify ((Over.mk g').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (Over.mk g').left.Etale,
        HasWeakSheafify ((Over.mk g').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))
    -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale, HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
        HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)))
    lowerShriekPullback g a g' b h_lower C.P_g Λ =
      (etaleDerivedLowerShriek (Over.mk g')
        (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g :
          (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk g').left.Etale, HasWeakSheafify ((Over.mk g').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk g').left.Etale,
      HasWeakSheafify ((Over.mk g').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale, HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)))
  by
  unfold etaleDerivedLowerShriek lowerShriekPullback
  unfold instHasDerivedCategory_compactificationPullback
  rfl


/-- Domain of the stacked-square compatibility: `(Rf_! ⋙ Rg_!) ⋙ a⁻¹`. -/
irreducible_def baseChange_compDomain :
    (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  compDomain X g C Λ ⋙ etaleModuleDerivedInverseImage a Λ


/-- Codomain of the stacked-square compatibility: `c⁻¹ ⋙ R(g' ∘ f')_!` of the
pasted compactification of `g ∘ f`. -/
irreducible_def baseChange_compCodomain :
    (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  etaleModuleDerivedInverseImage c Λ ⋙
    lowerShriekPullback (X.hom ≫ g) a (f' ≫ g') c
      (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C) Λ

-- Local declaration justification (definitional transport): Use the lower square's supplied instances directly, without selecting the upper-dependent spelling of the same ambient.
set_option backward.isDefEq.respectTransparency true in
/-- Lower stacked comparison `Rg_! ⋙ a⁻¹ ⟶ b⁻¹ ⋙ Rg'_!`, the compactification
model `baseChange` of the lower cartesian square. -/
@[irreducible]
def stacked_lowerBaseChange :
    -- Local instance justification (defeq pin): Use supplied `HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk g).left.Etale, HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (Over.mk g).left.Etale,
        HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
    (etaleDerivedLowerShriek (Over.mk g) C.P_g ⋙
      etaleModuleDerivedInverseImage a Λ) ⟶
    (etaleModuleDerivedInverseImage b Λ ⋙
      lowerShriekPullback g a g' b h_lower C.P_g Λ) :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk g).left.Etale, HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk g).left.Etale,
      HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- The local proof pins the existing restriction spelling; it adds no premise.
  -- Local instance justification (defeq pin): The lower mate reuses the supplied Kan-preservation proof at the canonical base-interior spelling.
  letI : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι C.P_g)).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι C.P_g)).op)
  by
    clear! f' c h_upper
    set_option backward.isDefEq.respectTransparency false in
      exact eqToHom (baseChangeDomain_def g a C.P_g Λ).symm ≫
        baseChange g a g' b h_lower C.P_g Λ
          (kanComposite := inferInstanceAs (∀ F : C.P_g.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
            (smallEtalePullback (b ≫ Of.ι C.P_g)).op.HasLeftKanExtension F)) ≫
        eqToHom (baseChangeCodomain_def g a g' b h_lower C.P_g Λ)

/-- Upper stacked comparison `Rf_! ⋙ b⁻¹ ⟶ c⁻¹ ⋙ Rf'_!`, the compactification
model `baseChange` of the upper cartesian square. -/
@[irreducible]
def stacked_upperBaseChange :
    -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk X.hom).left.Etale, HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (Over.mk X.hom).left.Etale,
        HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (ofInteriorHom X g C).obj.right.left.Etale, HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (ofInteriorHom X g C).obj.right.left.Etale,
        HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
    (etaleDerivedLowerShriek (Over.mk X.hom) (ofInteriorHom X g C) ⋙
      etaleModuleDerivedInverseImage b Λ) ⟶
    (etaleModuleDerivedInverseImage c Λ ⋙
      lowerShriekPullback X.hom b f' c h_upper (ofInteriorHom X g C) Λ) :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk X.hom).left.Etale, HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk X.hom).left.Etale,
      HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (ofInteriorHom X g C).obj.right.left.Etale, HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (ofInteriorHom X g C).obj.right.left.Etale,
      HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
  eqToHom (baseChangeDomain_def X.hom b (ofInteriorHom X g C) Λ).symm ≫
    baseChange X.hom b f' c h_upper (ofInteriorHom X g C) Λ ≫
    eqToHom (baseChangeCodomain_def X.hom b f' c h_upper (ofInteriorHom X g C) Λ)

-- Local declaration justification (localized automation): Compare the definitionally equal compactification ambient projections while retaining the supplied sheafification and localization choices in the pasted base-change map.
set_option backward.isDefEq.respectTransparency false in
/-- Pasted stacked comparison `R(g ∘ f)_! ⋙ a⁻¹ ⟶ c⁻¹ ⋙ R(g' ∘ f')_!`, the
compactification model `baseChange` of the outer rectangle. -/
@[irreducible]
def stacked_pasteBaseChange :
    -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk (X.hom ≫ g)).left.Etale, HasWeakSheafify ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (Over.mk (X.hom ≫ g)).left.Etale,
        HasWeakSheafify ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    -- Local instance justification (defeq pin): Use supplied `HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.ofComposite X g C).obj.right.left.Etale, HasWeakSheafify ((CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (CompDiagram.ofComposite X g C).obj.right.left.Etale,
        HasWeakSheafify ((CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    (etaleDerivedLowerShriek (Over.mk (X.hom ≫ g)) (CompDiagram.ofComposite X g C) ⋙
      etaleModuleDerivedInverseImage a Λ) ⟶
    (etaleModuleDerivedInverseImage c Λ ⋙
      lowerShriekPullback (X.hom ≫ g) a (f' ≫ g') c
        (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C) Λ) :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk (X.hom ≫ g)).left.Etale, HasWeakSheafify ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk (X.hom ≫ g)).left.Etale,
      HasWeakSheafify ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.ofComposite X g C).obj.right.left.Etale, HasWeakSheafify ((CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.ofComposite X g C).obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Use the supplied composite-interior restriction proof at its compactification alias.
  -- Local instance justification (defeq pin): Reuse the supplied Kan-extension property of the composite interior at its identical Of.ι spelling.
  letI : ∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the supplied Kan-extension property of the composite interior at its identical Of.ι spelling.
  letI : ∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse C.P_bar's given sheaf-composition proof at the identical ambient of CompDiagram.ofComposite.
  letI : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op)
  -- This is the same ambient as C.P_bar; reuse its given sheaf-composition proof.
  -- Local instance justification (defeq pin): Reuse C.P_bar's given sheaf-composition proof at the identical ambient of CompDiagram.ofComposite.
  letI : (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs (C.P_bar.obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  baseChangeUnfolded (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C) Λ

-- Local declaration justification (localized automation): Compare the definitionally equal interior ambient projections so both models use the supplied localization choice.
set_option backward.isDefEq.respectTransparency false in
-- Local declaration justification (module visibility): retain this implementation
-- equality privately while using its proof in the concrete public constructions.
set_option backward.privateInPublic true in
/-- The compactification model of `X.hom` from `CompDiagram.ofInterior` agrees
with `ofInteriorHom`. -/
private theorem ofInteriorHom_derived_eq :
    -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk X.hom).left.Etale, HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (Over.mk X.hom).left.Etale,
        HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
    -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (ofInteriorHom X g C).obj.right.left.Etale, HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (ofInteriorHom X g C).obj.right.left.Etale,
        HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
    -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
      inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale, HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
    letI : ∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale,
        HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
      fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
    -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
    letI : HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
      inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
    (etaleDerivedLowerShriek X (CompDiagram.ofInterior X g C) :
        (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) =
      (etaleDerivedLowerShriek (Over.mk X.hom) (ofInteriorHom X g C) :
        (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))) :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk X.hom).left.Etale, HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk X.hom).left.Etale,
      HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (ofInteriorHom X g C).obj.right.left.Etale, HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (ofInteriorHom X g C).obj.right.left.Etale,
      HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale, HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
  by
  rfl

/-- The composite of the upper and lower pullback compactification models. -/
irreducible_def stacked_factorShriek :
    (DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  lowerShriekPullback X.hom b f' c h_upper (ofInteriorHom X g C) Λ ⋙
    lowerShriekPullback g a g' b h_lower C.P_g Λ

/-- The compactification model of the composite after base change. -/
irreducible_def stacked_pasteShriek :
    (DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  lowerShriekPullback (X.hom ≫ g) a (f' ≫ g') c
    (h_upper.paste_vert h_lower)
    (CompDiagram.ofComposite X g C) Λ


-- Local declaration justification (module visibility): retain this implementation
-- equality privately while using its proof in the concrete public constructions.
set_option backward.privateInPublic true in
-- Local declaration justification (elaboration complexity): retain the explicit
-- model transports while checking their chosen localization data.
set_option maxHeartbeats 1500000 in
omit hasDerivedPushforwardBetweenAmbients in
/-- Whiskering the pasted compactification model by `c⁻¹` recovers the stacked
compatibility codomain. -/
private theorem stacked_pasteShriek_whisker_eq :
    (etaleModuleDerivedInverseImage c Λ ⋙
      stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ) =
      baseChange_compCodomain X g C f' g' a b c h_upper h_lower Λ := by
  rw [stacked_pasteShriek_def, baseChange_compCodomain_def]

/-- The original composition domain on the specified pulled-back diagram. -/
irreducible_def stacked_diagramDomain : (DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f').left.Etale, HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f').left.Etale,
      HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale, HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)))
  (@compDomain _ _ (Over.mk f') g' _ (inferInstanceAs (Scheme.Hom.FiniteType f'))) (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) Λ

/-- The original composition codomain on the same pulled-back diagram. -/
irreducible_def stacked_diagramCodomain : (DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f').left.Etale, HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f').left.Etale,
      HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale, HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)))
  (@compCodomain _ _ (Over.mk f') g' _ (inferInstanceAs (Scheme.Hom.FiniteType f'))) (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) Λ

/-- The composition comparison between the pulled-back domain and codomain models. -/
@[irreducible]
def stacked_diagramComp :
    stacked_diagramDomain X g C f' g' a b c h_upper h_lower Λ ⟶
      stacked_diagramCodomain X g C f' g' a b c h_upper h_lower Λ :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f').left.Etale, HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f').left.Etale,
      HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale, HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)))
  by
  rw [stacked_diagramDomain_def, stacked_diagramCodomain_def]
  -- The source forgetful functor uses the supplied sheaf-composition property on X'.
  exact @comp _ _ (Over.mk f') g'
    _ (inferInstanceAs (Scheme.Hom.FiniteType f')) _ _ _ _ _ _ _ _
    (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) Λ _
    _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _
    (inferInstanceAs (HasSheafCompose X'.smallEtaleTopology
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})))
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _


-- Local declaration justification (localized automation): Compare the fixed pullback compactification projections with the supplied raw interiorLift Kan extensions while preserving the ambient sheafification and localization choices.
-- Local declaration justification (elaboration complexity): checking the explicit
-- ambient transports requires reducing the fixed compactification projections.
set_option maxHeartbeats 1500000 in
-- Local declaration justification (elaboration complexity): retain the explicit
-- model transports while checking their chosen localization data.
set_option maxHeartbeats 1500000 in
/-- Transport the two factor models by the actual upper compactification isomorphism. -/
def stacked_pullbackCompDomainIso :
    stacked_factorShriek X g C f' g' a b c h_upper h_lower Λ ≅
      stacked_diagramDomain X g C f' g' a b c h_upper h_lower Λ :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f').left.Etale, HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f').left.Etale,
      HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk g').left.Etale, HasWeakSheafify ((Over.mk g').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk g').left.Etale,
      HasWeakSheafify ((Over.mk g').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk g').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale, HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)))
  by
  let e : (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) ≅ (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)) :=
    interiorCompactificationIso X g C f' g' a b c h_upper h_lower
  -- Local instance justification (defeq pin): Use supplied `Scheme.Hom.FiniteType f'` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofInterior (h_f_finiteType`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `Scheme.Hom.FiniteType f'` at definitionally identical `HasSheafify (CompDiagram.ofInterior (h_f_finiteType`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((CompDiagram.interior (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left.Etale,
      HasWeakSheafify ((compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient X.hom b f' c h_upper (ofInteriorHom X g C)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : ∀ F : X'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op)
  -- Local instance justification (defeq pin): Reuse the supplied Kan extensions of ambientToBase at (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.hom, the identical fixed map.
  letI : ∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.hom).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (ambientToBase X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C))'s given Kan extensions through this fixed ambient equivalence e to (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))'s proper map.
  letI : ∀ F : (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (Of.ι (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (interiorLift X.hom b f' c h_upper (ofInteriorHom X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C))'s given Kan extensions through this fixed ambient equivalence e to (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))'s proper map.
  letI : ∀ F : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom).op.HasLeftKanExtension F :=
    fun F => smallEtaleAmbient_hasLeftKanExtension (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.hom (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom
      (Of.ambientIso e) (Of.ambientIso_over e) F
  -- Local instance justification (defeq pin): Apply the existing Cartesian forward transfer at the identical fixed compactification (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)), retaining the supplied raw interiorLift exactness proof.
  letI : (etaleExtensionByZero (Of.ι (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C))) (ModuleCat.{u} Λ)).Additive :=
    instAdditive_etaleExtensionByZero_compactificationPullback_ι X.hom b f' c h_upper (ofInteriorHom X g C) Λ
  -- Local instance justification (defeq pin): Apply the existing Cartesian forward transfer at the identical fixed compactification (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)), retaining the supplied raw interiorLift exactness proof.
  letI : PreservesFiniteLimits (etaleExtensionByZero (Of.ι (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C))) (ModuleCat.{u} Λ)) :=
    instPreservesFiniteLimits_pullbackExtension X.hom b f' c h_upper (ofInteriorHom X g C) Λ
  -- Local instance justification (defeq pin): Apply the existing Cartesian forward transfer at the identical fixed compactification (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)), retaining the supplied raw interiorLift exactness proof.
  letI : PreservesFiniteColimits (etaleExtensionByZero (Of.ι (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C))) (ModuleCat.{u} Λ)) :=
    instPreservesFiniteColimits_pullbackExtension X.hom b f' c h_upper (ofInteriorHom X g C) Λ
  let v :
      etaleDerivedLowerShriek (Over.mk f') (Λ := Λ) (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)) ≅
        etaleDerivedLowerShriek (Over.mk f') (Λ := Λ) (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) :=
    CompactificationTransport.modelIso (X := X') (Y := Y') (Of.ι (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C))) (compactificationPullback X.hom b f' c h_upper (ofInteriorHom X g C)).obj.right.hom
    (Of.ι (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom (Of.ambientIso e)
    (Of.ambientIso_interior e) (Of.ambientIso_over e) Λ
  have lowerModel := stacked_lowerModel_eq X g C f' g' a b c h_upper h_lower Λ
  exact eqToIso (stacked_factorShriek_def X g C f' g' a b c h_upper h_lower Λ) ≪≫
    isoWhiskerRight v (lowerShriekPullback g a g' b h_lower C.P_g Λ) ≪≫
      isoWhiskerLeft (etaleDerivedLowerShriek (Over.mk f') (Λ := Λ) (CompDiagram.ofInterior (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))
        (eqToIso lowerModel) ≪≫
      (eqToIso ((@compDomain_def _ _ (Over.mk f') g' _ (inferInstanceAs (Scheme.Hom.FiniteType f'))) (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) Λ)).symm ≪≫
        (eqToIso (stacked_diagramDomain_def X g C f' g' a b c h_upper h_lower Λ)).symm

-- Local declaration justification (localized automation): Compare the fixed pullback compactification projections with the supplied raw interiorLift Kan extensions while preserving the ambient sheafification and localization choices.
-- Local declaration justification (elaboration complexity): checking the explicit
-- ambient transports requires reducing the fixed compactification projections.
set_option maxHeartbeats 1500000 in
/-- Transport the composite model by the actual iterated/direct ambient isomorphism. -/
def stacked_pullbackCompCodomainIso :
    stacked_diagramCodomain X g C f' g' a b c h_upper h_lower Λ ≅
      stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk f').left.Etale, HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk f').left.Etale,
      HasWeakSheafify ((Over.mk f').left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk f').left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk (f' ≫ g')).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk (f' ≫ g')).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk (f' ≫ g')).left.Etale, HasWeakSheafify ((Over.mk (f' ≫ g')).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk (f' ≫ g')).left.Etale,
      HasWeakSheafify ((Over.mk (f' ≫ g')).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk (f' ≫ g')).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk (f' ≫ g')).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale, HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient g a g' b h_lower C.P_g).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (ambient g a g' b h_lower C.P_g).smallEtaleTopology (ModuleCat.{u} Λ)))
  by
  -- Local instance justification (defeq pin): Use the open-immersion proof stored in the fixed compactification (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) at its interior-map spelling.
  letI compositeOpenImmersion : IsOpenImmersion (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) := Of.instIsOpenImmersion Z' (Over.mk (f' ≫ g')) (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))
  let e : (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) ≅ (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)) :=
    compositeCompactificationIso X g C f' g' a b c h_upper h_lower
  -- Local instance justification (defeq pin): Use supplied `Scheme.Hom.FiniteType f'` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofComposite (h_f_finiteType`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `Scheme.Hom.FiniteType f'` at definitionally identical `HasSheafify (CompDiagram.ofComposite (h_f_finiteType`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify ((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs (((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs (((CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : HasSheafify (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.left.smallEtaleTopology AddCommGrpCat.{u} :=
    inferInstanceAs (HasSheafify (ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology AddCommGrpCat.{u})
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : ∀ U : (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.left.Etale,
      HasWeakSheafify ((compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Reuse the given site property on this identical fixed ambient; avoid a second generic sheafification search.
  letI : (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.left.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI : (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.left.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}) :=
    inferInstanceAs ((ambient (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))

  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI compositeRestrictionKanModule : ∀ F : (Over.mk (f' ≫ g')).left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (etaleRestriction (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI compositeRestrictionKanAdd : ∀ F : (Over.mk (f' ≫ g')).left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (etaleRestriction (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((etaleRestriction (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op.HasLeftKanExtension F)
  -- Local instance justification (defeq pin): Reuse the given restriction and Kan-extension property at the interior map of this fixed compactification.
  letI compositeRestrictionPreservesKan : (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op :=
    inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (etaleRestriction (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op)
  -- Local instance justification (defeq pin): Reuse the supplied Kan extensions of ambientToBase at (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.hom, the identical fixed map.
  letI : ∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.hom).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (ambientToBase (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))'s given Kan extensions through this fixed ambient equivalence e to (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))'s proper map.
  letI : ∀ F : (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (Of.ι (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)))).op.HasLeftKanExtension F :=
    fun F => inferInstanceAs
      ((smallEtalePullback (interiorLift (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  -- Local instance justification (proof-local temporary data): Transfer (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))'s given Kan extensions through this fixed ambient equivalence e to (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))'s proper map.
  letI compositePushforwardKan : ∀ F : Z'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom).op.HasLeftKanExtension F :=
    fun F => smallEtaleAmbient_hasLeftKanExtension (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.hom (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom
      (Of.ambientIso e) (Of.ambientIso_over e) F
  -- Local instance justification (defeq pin): Reuse the exactness property of the specified composite interior at the identical map (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).ι.
  letI compositeExtensionAdditive : (etaleExtensionByZero (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) (ModuleCat.{u} Λ)).Additive :=
    inferInstanceAs ((etaleExtensionByZero
      (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))
      (ModuleCat.{u} Λ)).Additive)
  -- Local instance justification (defeq pin): Reuse the exactness property of the specified composite interior at the identical map (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).ι.
  letI compositeExtensionLimits : PreservesFiniteLimits (etaleExtensionByZero (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) (ModuleCat.{u} Λ)) :=
    inferInstanceAs (PreservesFiniteLimits (etaleExtensionByZero
      (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))
      (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Reuse the exactness property of the specified composite interior at the identical map (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).ι.
  letI compositeExtensionColimits : PreservesFiniteColimits (etaleExtensionByZero (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) (ModuleCat.{u} Λ)) :=
    inferInstanceAs (PreservesFiniteColimits (etaleExtensionByZero
      (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))
      (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Apply the existing Cartesian forward transfer at the identical fixed compactification (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)), retaining the supplied raw interiorLift exactness proof.
  letI : (etaleExtensionByZero (Of.ι (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))) (ModuleCat.{u} Λ)).Additive :=
    instAdditive_etaleExtensionByZero_compactificationPullback_ι (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C) Λ
  -- Local instance justification (defeq pin): Apply the existing Cartesian forward transfer at the identical fixed compactification (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)), retaining the supplied raw interiorLift exactness proof.
  letI : PreservesFiniteLimits (etaleExtensionByZero (Of.ι (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))) (ModuleCat.{u} Λ)) :=
    instPreservesFiniteLimits_pullbackExtension (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C) Λ
  -- Local instance justification (defeq pin): Apply the existing Cartesian forward transfer at the identical fixed compactification (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)), retaining the supplied raw interiorLift exactness proof.
  letI : PreservesFiniteColimits (etaleExtensionByZero (Of.ι (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))) (ModuleCat.{u} Λ)) :=
    instPreservesFiniteColimits_pullbackExtension (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C) Λ
  -- Local instance justification (proof-local temporary data): Derive étaleness of the specified composite interior from its canonical open immersion for the ambient inverse-image comparison.
  letI compositeEtale : Etale (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) :=
    instEtale_ι (f' ≫ g') (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))
  -- Local instance justification (proof-local temporary data): Use the canonical small-étale module pullback Kan extensions for this composite interior, using the preceding étale proof.
  letI compositeInverseImageKan : ∀ F : (CompDiagram.pullback X g C f' g' a b c h_upper h_lower).P_bar.obj.right.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback (Of.ι (CompDiagram.ofComposite.{u} (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)))).op.HasLeftKanExtension F :=
    fun F => smallEtaleModulePullbackHasLeftKanExtension (A := X') (Of.ι (CompDiagram.ofComposite.{u} (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) Λ F
  let v :
      etaleDerivedLowerShriek (Over.mk (f' ≫ g')) (Λ := Λ) (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)) ≅
        etaleDerivedLowerShriek (Over.mk (f' ≫ g')) (Λ := Λ) (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)) :=
    CompactificationTransport.modelIso (X := X') (Y := Z') (targetOpenImmersion := compositeOpenImmersion) (targetInverseImageKan := compositeInverseImageKan) (targetPushforwardKan := compositePushforwardKan) (targetRestrictionKanModule := compositeRestrictionKanModule) (targetRestrictionKanAdd := compositeRestrictionKanAdd) (targetRestrictionPreservesKan := compositeRestrictionPreservesKan) (targetExtensionAdditive := compositeExtensionAdditive) (targetExtensionLimits := compositeExtensionLimits) (targetExtensionColimits := compositeExtensionColimits) (Of.ι (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C))) (compactificationPullback (X.hom ≫ g) a (f' ≫ g') c (h_upper.paste_vert h_lower) (CompDiagram.ofComposite X g C)).obj.right.hom
      (Of.ι (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower))) (CompDiagram.ofComposite (h_f_finiteType := inferInstanceAs (Scheme.Hom.FiniteType f')) (Over.mk f') g' (CompDiagram.pullback X g C f' g' a b c h_upper h_lower)).obj.right.hom (Of.ambientIso e)
      (Of.ambientIso_interior e) (Of.ambientIso_over e) Λ
  exact eqToIso (stacked_diagramCodomain_def X g C f' g' a b c h_upper h_lower Λ) ≪≫
    eqToIso ((@compCodomain_def _ _ (Over.mk f') g' _ (inferInstanceAs (Scheme.Hom.FiniteType f'))) (CompDiagram.pullback X g C f' g' a b c h_upper h_lower) Λ) ≪≫ v.symm ≪≫
    (eqToIso (stacked_pasteShriek_def X g C f' g' a b c h_upper h_lower Λ)).symm

/-- Composition comparison of the base-changed compactification diagram of
`f'` and `g'`. -/
@[irreducible]
def stacked_pullbackComp :
    stacked_factorShriek X g C f' g' a b c h_upper h_lower Λ ⟶
      stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ :=
  (stacked_pullbackCompDomainIso X g C f' g' a b c h_upper h_lower Λ).hom ≫
    stacked_diagramComp X g C f' g' a b c h_upper h_lower Λ ≫
    (stacked_pullbackCompCodomainIso X g C f' g' a b c h_upper h_lower Λ).hom


/-- The outer path composes the model comparison with base change for the composite. -/
@[irreducible]
def baseChange_comp_outer :
    baseChange_compDomain X g C a Λ ⟶
      baseChange_compCodomain X g C f' g' a b c h_upper h_lower Λ :=
  eqToHom (baseChange_compDomain_def X g C a Λ) ≫
    whiskerRight (comp X g C Λ) (etaleModuleDerivedInverseImage a Λ) ≫
    whiskerRight (eqToHom (compCodomain_def X g C Λ))
      (etaleModuleDerivedInverseImage a Λ) ≫
    stacked_pasteBaseChange X g C f' g' a b c h_upper h_lower Λ ≫
    eqToHom (baseChange_compCodomain_def X g C f' g' a b c h_upper h_lower Λ).symm

-- Local declaration justification (elaboration complexity): compare the actual
-- factor models with the composition domain by definitional reduction.
set_option maxHeartbeats 1500000 in
/-- The inner path uses base change for both factors and the pulled-back composition comparison. -/
@[irreducible]
def baseChange_comp_inner :
    baseChange_compDomain X g C a Λ ⟶
      baseChange_compCodomain X g C f' g' a b c h_upper h_lower Λ :=
  -- Local instance justification (defeq pin): Use supplied `HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk g).left.Etale, HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk g).left.Etale,
      HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk X.hom).left.Etale, HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk X.hom).left.Etale,
      HasWeakSheafify ((Over.mk X.hom).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk X.hom).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (ofInteriorHom X g C).obj.right.left.Etale, HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (ofInteriorHom X g C).obj.right.left.Etale,
      HasWeakSheafify ((ofInteriorHom X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (ofInteriorHom X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale, HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
  let F : (DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
    etaleDerivedLowerShriek X (Λ := Λ) (CompDiagram.ofInterior X g C)
  let G : (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) :=
    etaleDerivedLowerShriek (Over.mk g) (Λ := Λ) C.P_g
  let A := etaleModuleDerivedInverseImage a Λ
  let B := etaleModuleDerivedInverseImage b Λ
  let Cinv := etaleModuleDerivedInverseImage c Λ
  let F' : (DerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
    lowerShriekPullback X.hom b f' c h_upper (ofInteriorHom X g C) Λ
  let G' : (DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) ⥤ (DerivedCategory (Sheaf Z'.smallEtaleTopology (ModuleCat.{u} Λ))) :=
    lowerShriekPullback g a g' b h_lower C.P_g Λ
  let lower : ((F ⋙ G) ⋙ A) ⟶ ((F ⋙ B) ⋙ G') :=
    (Functor.associator F G A).hom ≫
      whiskerLeft F (stacked_lowerBaseChange X g C g' a b h_lower Λ) ≫
      (Functor.associator F B G').inv
  let upper : ((F ⋙ B) ⋙ G') ⟶ (Cinv ⋙ (F' ⋙ G')) :=
    whiskerRight (whiskerRight (eqToHom (ofInteriorHom_derived_eq X g C Λ)) B) G' ≫
      whiskerRight (stacked_upperBaseChange X g C f' b c h_upper Λ) G' ≫
      (Functor.associator Cinv F' G').hom
  let paste : (Cinv ⋙ (F' ⋙ G')) ⟶
      (Cinv ⋙ stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ) :=
    whiskerLeft Cinv
      (eqToHom (stacked_factorShriek_def X g C f' g' a b c h_upper h_lower Λ).symm ≫
        stacked_pullbackComp X g C f' g' a b c h_upper h_lower Λ)
  let unfolded : (compDomain X g C Λ ⋙ A) ⟶
      (Cinv ⋙ stacked_pasteShriek X g C f' g' a b c h_upper h_lower Λ) :=
    whiskerRight (eqToHom (compDomain_def X g C Λ)) A ≫ lower ≫ upper ≫ paste
  eqToHom (baseChange_compDomain_def X g C a Λ) ≫ unfolded ≫
    eqToHom (stacked_pasteShriek_whisker_eq X g C f' g' a b c h_upper h_lower Λ)

/-- The outer pasted base-change path equals the inner path through the
factor base-change mates and the composition comparison of `C` on admissible complexes. -/
theorem baseChange_comp :
    whiskerLeft (Derived.compactSupportAdmissible X.left Λ).ι
      (baseChange_comp_outer X g C f' g' a b c h_upper h_lower Λ) =
    whiskerLeft (Derived.compactSupportAdmissible X.left Λ).ι
      (baseChange_comp_inner X g C f' g' a b c h_upper h_lower Λ) :=
  sorry


end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek
end
