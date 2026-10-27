/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ModuleSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero.LowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.Pushforward.Composition
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ProperLowerShriek
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Composition

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology CategoryTheory.Sheaf
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

-- Local declaration justification (localized automation): match the chosen derived categories
-- across the definitionally equal projections of `Over.mk` and `Of.mk`.
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
variable [IsSeparated g] [Scheme.Hom.FiniteType g]
variable [h_X_compact : CompactSpace X.left] [h_X_quasiSeparated : QuasiSeparatedSpace X.left]
variable [CompactSpace Y] [QuasiSeparatedSpace Y]
variable [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g)

variable (Λ : Type u) [Ring Λ]
variable [HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.left.Etale,
  HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify Z.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : Z.Etale,
  HasWeakSheafify (Z.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : (CompDiagram.interior X g C).Etale,
  HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : C.P_bar.obj.right.left.Etale,
  HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : C.P_g.obj.right.left.Etale,
  HasWeakSheafify (C.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]

  [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify (CompDiagram.interior X g C).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify C.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafCompose X.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose Y.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose (CompDiagram.interior X g C).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose C.P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose C.P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior X g C).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]

  [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior X g C).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion X g C)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι C.P_g)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion X g C)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι C.P_g)).op]


/-- Derived Leray identification `Rf̄_* ⋙ Rḡ_* ≅ R(f̄ ≫ ḡ)_*`. -/
def pushforwardCompIso :
    (etaleDerivedPushforward C.P_bar.obj.right.hom :
          DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward C.P_g.obj.right.hom :
          DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) ≅
      (etaleDerivedPushforward (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) :
        DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  (asIso
      (etaleDerivedPushforwardComp C.P_bar.obj.right.hom C.P_g.obj.right.hom Λ :
        (etaleDerivedPushforward (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom) :
            DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) ⟶
          (etaleDerivedPushforward C.P_bar.obj.right.hom :
                DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
                  DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
            (etaleDerivedPushforward C.P_g.obj.right.hom :
              DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))))).symm


/-- Whiskered proper/open square comparison on the open/proper square of a
composition diagram, transported to the extension-by-zero model. -/
def squareMap :
    (etaleDerivedPushforward (X := (CompDiagram.interior X g C)) (Y := Y) (CompDiagram.toBase X g C) :
          DerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleExtensionByZero (U := Y) (X := C.P_g.obj.right.left) (Of.ι C.P_g) (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      (etaleExtensionByZero (U := (CompDiagram.interior X g C)) (X := C.P_bar.obj.right.left) (CompDiagram.openImmersion X g C)
            (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleDerivedPushforward C.P_bar.obj.right.hom :
          DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
            DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  (whiskerLeft
      (etaleDerivedPushforward (X := (CompDiagram.interior X g C)) (Y := Y) (CompDiagram.toBase X g C))
      (extensionByZeroDerivedIsoLowerShriekModule (U := Y) (T := C.P_g.obj.right.left) (Of.ι C.P_g) Λ).hom ≫
    (@etaleDerivedLowerShriekPushforward C.P_bar.obj.right.left C.P_g.obj.right.left
      (CompDiagram.interior X g C) Y C.P_bar.obj.right.hom
      (CompDiagram.toBase X g C) (Of.ι C.P_g)
      (CompDiagram.openImmersion X g C) (CompDiagram.square X g C)
      inferInstance (CompDiagram.isProper_toBase X g C)) Λ ≫
    whiskerRight
      (extensionByZeroDerivedIsoLowerShriekModule (U := (CompDiagram.interior X g C)) (T := C.P_bar.obj.right.left)
          (CompDiagram.openImmersion X g C) Λ).inv
      (etaleDerivedPushforward C.P_bar.obj.right.hom))


/-- Derived identification `j_! ⋙ j'_! ⟶ (j' ∘ j)_!` in the extension-by-zero
model. -/
def shriekComp :
    (etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C))
            (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
        (etaleExtensionByZero (U := (CompDiagram.interior X g C)) (X := C.P_bar.obj.right.left) (CompDiagram.openImmersion X g C)
            (ModuleCat.{u} Λ)).mapDerivedCategory ⟶
      (etaleExtensionByZero (U := X.left) (X := C.P_bar.obj.right.left)
          (Of.ι (CompDiagram.ofInterior X g C) ≫ CompDiagram.openImmersion X g C)
          (ModuleCat.{u} Λ)).mapDerivedCategory :=
  whiskerRight
      (extensionByZeroDerivedIsoLowerShriekModule (U := X.left) (T := (CompDiagram.interior X g C))
          (Of.ι (CompDiagram.ofInterior X g C)) Λ).hom
      (etaleExtensionByZero (U := (CompDiagram.interior X g C)) (X := C.P_bar.obj.right.left) (CompDiagram.openImmersion X g C)
          (ModuleCat.{u} Λ)).mapDerivedCategory ≫
    whiskerLeft (lowerShriekModuleDerived (X := X.left) (Y := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C)) Λ)
      (extensionByZeroDerivedIsoLowerShriekModule (U := (CompDiagram.interior X g C)) (T := C.P_bar.obj.right.left)
          (CompDiagram.openImmersion X g C) Λ).hom ≫
    (lowerShriekModuleDerivedCompIso (X := X.left) (Y := (CompDiagram.interior X g C)) (Z := C.P_bar.obj.right.left) (Of.ι (CompDiagram.ofInterior X g C))
        (CompDiagram.openImmersion X g C) Λ).hom ≫
    (extensionByZeroDerivedIsoLowerShriekModule (U := X.left) (T := C.P_bar.obj.right.left)
        (Of.ι (CompDiagram.ofInterior X g C) ≫ CompDiagram.openImmersion X g C) Λ).inv


/-- Compactification model of `Rf_! ⋙ Rg_!`. -/
irreducible_def compDomain :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C))
      (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
      etaleDerivedPushforward (X := (CompDiagram.interior X g C)) (Y := Y) (CompDiagram.toBase X g C)) ⋙
    ((etaleExtensionByZero (U := Y) (X := C.P_g.obj.right.left) (Of.ι C.P_g)
      (ModuleCat.{u} Λ)).mapDerivedCategory ⋙ etaleDerivedPushforward C.P_g.obj.right.hom)


/-- Compactification model of `R(g ∘ f)_!`. -/
irreducible_def compCodomain :
    DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)) :=
  ((etaleExtensionByZero (U := X.left) (X := C.P_bar.obj.right.left)
      (Of.ι (CompDiagram.ofComposite X g C)) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
      etaleDerivedPushforward (C.P_bar.obj.right.hom ≫ C.P_g.obj.right.hom))


-- Local declaration justification (localized automation): reassociation of the explicit
-- derived functors requires unfolding their compactification projections.
set_option maxHeartbeats 1000000 in
/-- Canonical comparison `Rf_! ⋙ Rg_! ⟶ R(g ∘ f)_!` of compactification models
attached to a composition diagram. -/
@[irreducible]
def comp : compDomain X g C Λ ⟶ compCodomain X g C Λ :=
  eqToHom (compDomain_def X g C Λ) ≫
  ((Functor.associator
      (etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)).mapDerivedCategory
      (etaleDerivedPushforward (X := (CompDiagram.interior X g C)) (Y := Y) (CompDiagram.toBase X g C) :
        DerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
      (((etaleExtensionByZero (U := Y) (X := C.P_g.obj.right.left) (Of.ι C.P_g)
      (ModuleCat.{u} Λ)).mapDerivedCategory ⋙ etaleDerivedPushforward C.P_g.obj.right.hom) :
        DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
    whiskerLeft
      (etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)).mapDerivedCategory
      ((Functor.associator
          (etaleDerivedPushforward (X := (CompDiagram.interior X g C)) (Y := Y) (CompDiagram.toBase X g C) :
            DerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
          (etaleExtensionByZero (U := Y) (X := C.P_g.obj.right.left) (Of.ι C.P_g) (ModuleCat.{u} Λ)).mapDerivedCategory
          (etaleDerivedPushforward C.P_g.obj.right.hom :
            DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).inv ≫
        whiskerRight (squareMap X g C Λ)
          (etaleDerivedPushforward C.P_g.obj.right.hom :
            DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
        (Functor.associator
            (etaleExtensionByZero (U := (CompDiagram.interior X g C)) (X := C.P_bar.obj.right.left) (CompDiagram.openImmersion X g C)
                (ModuleCat.{u} Λ)).mapDerivedCategory
            (etaleDerivedPushforward C.P_bar.obj.right.hom :
              DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
                DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
            (etaleDerivedPushforward C.P_g.obj.right.hom :
              DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).hom) ≫
    (Functor.associator
        (etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)).mapDerivedCategory
        (etaleExtensionByZero (U := (CompDiagram.interior X g C)) (X := C.P_bar.obj.right.left) (CompDiagram.openImmersion X g C) (ModuleCat.{u} Λ)).mapDerivedCategory
        ((etaleDerivedPushforward C.P_bar.obj.right.hom :
              DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
                DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
          (etaleDerivedPushforward C.P_g.obj.right.hom :
            DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))))).inv ≫
    whiskerRight (shriekComp X g C Λ)
      ((etaleDerivedPushforward C.P_bar.obj.right.hom :
            DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
              DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward C.P_g.obj.right.hom :
          DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))) ≫
    whiskerLeft
      (etaleExtensionByZero (U := X.left) (X := C.P_bar.obj.right.left)
          (Of.ι (CompDiagram.ofInterior X g C) ≫ CompDiagram.openImmersion X g C)
          (ModuleCat.{u} Λ)).mapDerivedCategory
      (pushforwardCompIso X g C Λ).hom) ≫
    eqToHom (compCodomain_def X g C Λ).symm


/-- Component of `comp` at an object of `D(X_étale, Λ)`. -/
@[irreducible]
def comp_app (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (compDomain X g C Λ).obj K ⟶ (compCodomain X g C Λ).obj K :=
  (comp X g C Λ).app K


/-- The objectwise comparison is the component of `comp`. -/
theorem comp_app_eq (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) :
    comp_app X g C Λ K = (comp X g C Λ).app K :=
  sorry


-- Local declaration justification (localized automation): reassociation of the explicit
-- derived functors requires unfolding their compactification projections.
set_option maxHeartbeats 1000000 in
/-- Unfolding of `comp` as the whiskered proper/open square map together with the
shriek and pushforward composition identifications. -/
theorem comp_eq :
    eqToHom (compDomain_def X g C Λ).symm ≫
        comp X g C Λ ≫ eqToHom (compCodomain_def X g C Λ) =
      (Functor.associator
          (etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C))
              (ModuleCat.{u} Λ)).mapDerivedCategory
          (etaleDerivedPushforward (X := (CompDiagram.interior X g C)) (Y := Y) (CompDiagram.toBase X g C) :
            DerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
          (((etaleExtensionByZero (U := Y) (X := C.P_g.obj.right.left) (Of.ι C.P_g)
      (ModuleCat.{u} Λ)).mapDerivedCategory ⋙ etaleDerivedPushforward C.P_g.obj.right.hom) :
            DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).hom ≫
        whiskerLeft
          (etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C))
              (ModuleCat.{u} Λ)).mapDerivedCategory
          ((Functor.associator
              (etaleDerivedPushforward (X := (CompDiagram.interior X g C)) (Y := Y) (CompDiagram.toBase X g C) :
                DerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
              (etaleExtensionByZero (U := Y) (X := C.P_g.obj.right.left) (Of.ι C.P_g) (ModuleCat.{u} Λ)).mapDerivedCategory
              (etaleDerivedPushforward C.P_g.obj.right.hom :
                DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).inv ≫
            whiskerRight (squareMap X g C Λ)
              (etaleDerivedPushforward C.P_g.obj.right.hom :
                DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
            (Functor.associator
                (etaleExtensionByZero (U := (CompDiagram.interior X g C)) (X := C.P_bar.obj.right.left) (CompDiagram.openImmersion X g C)
                    (ModuleCat.{u} Λ)).mapDerivedCategory
                (etaleDerivedPushforward C.P_bar.obj.right.hom :
                  DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
                    DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
                (etaleDerivedPushforward C.P_g.obj.right.hom :
                  DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))).hom) ≫
        (Functor.associator
            (etaleExtensionByZero (U := X.left) (X := (CompDiagram.interior X g C)) (Of.ι (CompDiagram.ofInterior X g C))
                (ModuleCat.{u} Λ)).mapDerivedCategory
            (etaleExtensionByZero (U := (CompDiagram.interior X g C)) (X := C.P_bar.obj.right.left) (CompDiagram.openImmersion X g C)
                (ModuleCat.{u} Λ)).mapDerivedCategory
            ((etaleDerivedPushforward C.P_bar.obj.right.hom :
                  DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
                    DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
              (etaleDerivedPushforward C.P_g.obj.right.hom :
                DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ))))).inv ≫
        whiskerRight (shriekComp X g C Λ)
          ((etaleDerivedPushforward C.P_bar.obj.right.hom :
                DerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤
                  DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
            (etaleDerivedPushforward C.P_g.obj.right.hom :
              DerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))) ≫
        whiskerLeft
          (etaleExtensionByZero (U := X.left) (X := C.P_bar.obj.right.left)
              (Of.ι (CompDiagram.ofInterior X g C) ≫ CompDiagram.openImmersion X g C)
              (ModuleCat.{u} Λ)).mapDerivedCategory
          (pushforwardCompIso X g C Λ).hom :=
  sorry


include h_X_compact h_X_quasiSeparated in
/-- The comparison `Rf_! ⋙ Rg_! ⟶ R(g ∘ f)_!` is an isomorphism on objects
of `D⁺_tors(X_étale, Λ)`. -/
theorem comp_isIso_of_isGE_isTorsion
    (K : DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))) (h_tors : etaleDerivedIsTorsion K) (n : ℤ)
    [DerivedCategory.IsGE K n] :
    IsIso (comp_app X g C Λ K) :=
  sorry


include h_X_compact h_X_quasiSeparated in
/-- If `Λ` is a torsion ring, the comparison `Rf_! ⋙ Rg_! ⟶ R(g ∘ f)_!` is
an isomorphism of functors on `D(X_étale, Λ)`. -/
theorem comp_isIso_of_isTorsion
    (hΛ : AddMonoid.IsTorsion Λ) :
    IsIso (comp X g C Λ) :=
  sorry


/-- If `Λ` is a torsion ring, package `comp` as an isomorphism of
compactification models. -/
def compIso (hΛ : AddMonoid.IsTorsion Λ) :
    compDomain X g C Λ ≅ compCodomain X g C Λ :=
  @asIso _ _ _ _ (comp X g C Λ) (comp_isIso_of_isTorsion X g C Λ hΛ)


end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

end
