/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Composition

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


variable (D : CompDiagram X g)
variable [HasSheafify (CompDiagram.interior X g D).smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : (CompDiagram.interior X g D).Etale,
  HasWeakSheafify ((CompDiagram.interior X g D).smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf (CompDiagram.interior X g D).smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify D.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : D.P_bar.obj.right.left.Etale,
  HasWeakSheafify (D.P_bar.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf D.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify D.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : D.P_g.obj.right.left.Etale,
  HasWeakSheafify (D.P_g.obj.right.left.smallEtaleTopology.over U)
    (ModuleCat.{u} Λ)]
variable [HasDerivedCategory
  (Sheaf D.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasSheafify (CompDiagram.interior X g D).smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify D.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify D.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafCompose (CompDiagram.interior X g D).smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose D.P_bar.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafCompose D.P_g.obj.right.left.smallEtaleTopology
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [(CompDiagram.interior X g D).smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [D.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [D.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g D))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior X g D).Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (CompDiagram.openImmersion X g D)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g D))).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (etaleRestriction (Of.ι D.P_g)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g D))).op.HasLeftKanExtension F]
variable [∀ F : (CompDiagram.interior X g D).Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (CompDiagram.openImmersion X g D)).op.HasLeftKanExtension F]
variable [∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g D))).op.HasLeftKanExtension F]
variable [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (etaleRestriction (Of.ι D.P_g)).op.HasLeftKanExtension F]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofInterior X g D))).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (CompDiagram.openImmersion X g D)).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι (CompDiagram.ofComposite X g D))).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (etaleRestriction (Of.ι D.P_g)).op]

/-- Compatible diagram morphisms induce transitions between the interior compactification models. -/
private def diagramInteriorTransition (φ : CompDiagram.DiagramHom X g C D) :=
  let hSourceSheafify := inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
  let hSourceOver := inferInstanceAs (∀ V : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hSourceDerived := inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hSourceCompose := inferInstanceAs (HasSheafCompose X.left.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hTargetDerived := inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hPSheafify := inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
  let hPOver := inferInstanceAs (∀ V : (CompDiagram.interior X g C).Etale, HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hPDerived := inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
  let hPAbelian := inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology AddCommGrpCat.{u})
  let hPCompose := inferInstanceAs (HasSheafCompose (CompDiagram.interior X g C).smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hPPreserves := inferInstanceAs ((CompDiagram.interior X g C).smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hQSheafify := inferInstanceAs (HasSheafify (CompDiagram.interior X g D).smallEtaleTopology (ModuleCat.{u} Λ))
  let hQOver := inferInstanceAs (∀ V : (CompDiagram.interior X g D).Etale, HasWeakSheafify ((CompDiagram.interior X g D).smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hQDerived := inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g D).smallEtaleTopology (ModuleCat.{u} Λ)))
  let hQAbelian := inferInstanceAs (HasSheafify (CompDiagram.interior X g D).smallEtaleTopology AddCommGrpCat.{u})
  let hQCompose := inferInstanceAs (HasSheafCompose (CompDiagram.interior X g D).smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hQPreserves := inferInstanceAs ((CompDiagram.interior X g D).smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hPModuleKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F)
  let hPAbelianKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op.HasLeftKanExtension F)
  let hPKanCompose := inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g C))).op)
  let hQModuleKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g D))).op.HasLeftKanExtension F)
  let hQAbelianKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g D))).op.HasLeftKanExtension F)
  let hQKanCompose := inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι (CompDiagram.ofInterior X g D))).op)
  @isoOfHom Y X Λ inferInstance (CompDiagram.ofInterior X g C) (CompDiagram.ofInterior X g D) φ.homInterior
    hSourceSheafify hSourceOver hSourceDerived
    hPSheafify hPOver hPDerived hQSheafify hQOver hQDerived hTargetDerived
    hPModuleKan hQModuleKan hSourceCompose hPCompose hQCompose
    (inferInstanceAs (HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}))
    hPAbelian hQAbelian hPPreserves hQPreserves
    hPAbelianKan hQAbelianKan hPKanCompose hQKanCompose
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- Compatible diagram morphisms induce transitions between the base compactification models. -/
private def diagramBaseTransition (φ : CompDiagram.DiagramHom X g C D) :=
  let hSourceSheafify := inferInstanceAs (HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ))
  let hSourceOver := inferInstanceAs (∀ V : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hSourceDerived := inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hSourceCompose := inferInstanceAs (HasSheafCompose Y.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hTargetDerived := inferInstanceAs (HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hPSheafify := inferInstanceAs (HasSheafify C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
  let hPOver := inferInstanceAs (∀ V : C.P_g.obj.right.left.Etale, HasWeakSheafify (C.P_g.obj.right.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hPDerived := inferInstanceAs (HasDerivedCategory (Sheaf C.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hPAbelian := inferInstanceAs (HasSheafify C.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})
  let hPCompose := inferInstanceAs (HasSheafCompose C.P_g.obj.right.left.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hPPreserves := inferInstanceAs (C.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hQSheafify := inferInstanceAs (HasSheafify D.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
  let hQOver := inferInstanceAs (∀ V : D.P_g.obj.right.left.Etale, HasWeakSheafify (D.P_g.obj.right.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hQDerived := inferInstanceAs (HasDerivedCategory (Sheaf D.P_g.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hQAbelian := inferInstanceAs (HasSheafify D.P_g.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})
  let hQCompose := inferInstanceAs (HasSheafCompose D.P_g.obj.right.left.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hQPreserves := inferInstanceAs (D.P_g.obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hPModuleKan := inferInstanceAs (∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι (C.P_g))).op.HasLeftKanExtension F)
  let hPAbelianKan := inferInstanceAs (∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι (C.P_g))).op.HasLeftKanExtension F)
  let hPKanCompose := inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι (C.P_g))).op)
  let hQModuleKan := inferInstanceAs (∀ F : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι (D.P_g))).op.HasLeftKanExtension F)
  let hQAbelianKan := inferInstanceAs (∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι (D.P_g))).op.HasLeftKanExtension F)
  let hQKanCompose := inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι (D.P_g))).op)
  @isoOfHom Z (Over.mk g) Λ inferInstance C.P_g D.P_g φ.homBase
    hSourceSheafify hSourceOver hSourceDerived
    hPSheafify hPOver hPDerived hQSheafify hQOver hQDerived hTargetDerived
    hPModuleKan hQModuleKan hSourceCompose hPCompose hQCompose
    (inferInstanceAs (HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}))
    hPAbelian hQAbelian hPPreserves hQPreserves
    hPAbelianKan hQAbelianKan hPKanCompose hQKanCompose
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- Compatible diagram morphisms induce transitions between the composite compactification models. -/
private def diagramCompositeTransition (φ : CompDiagram.DiagramHom X g C D) :=
  let hSourceSheafify := inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
  let hSourceOver := inferInstanceAs (∀ V : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hSourceDerived := inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hSourceCompose := inferInstanceAs (HasSheafCompose X.left.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hTargetDerived := inferInstanceAs (HasDerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hPSheafify := inferInstanceAs (HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
  let hPOver := inferInstanceAs (∀ V : C.P_bar.obj.right.left.Etale, HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hPDerived := inferInstanceAs (HasDerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hPAbelian := inferInstanceAs (HasSheafify C.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})
  let hPCompose := inferInstanceAs (HasSheafCompose C.P_bar.obj.right.left.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hPPreserves := inferInstanceAs (C.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hQSheafify := inferInstanceAs (HasSheafify D.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
  let hQOver := inferInstanceAs (∀ V : D.P_bar.obj.right.left.Etale, HasWeakSheafify (D.P_bar.obj.right.left.smallEtaleTopology.over V) (ModuleCat.{u} Λ))
  let hQDerived := inferInstanceAs (HasDerivedCategory (Sheaf D.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  let hQAbelian := inferInstanceAs (HasSheafify D.P_bar.obj.right.left.smallEtaleTopology AddCommGrpCat.{u})
  let hQCompose := inferInstanceAs (HasSheafCompose D.P_bar.obj.right.left.smallEtaleTopology (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hQPreserves := inferInstanceAs (D.P_bar.obj.right.left.smallEtaleTopology.PreservesSheafification (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}))
  let hPModuleKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  let hPAbelianKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op.HasLeftKanExtension F)
  let hPKanCompose := inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι (CompDiagram.ofComposite X g C))).op)
  let hQModuleKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
    (etaleRestriction (Of.ι (CompDiagram.ofComposite X g D))).op.HasLeftKanExtension F)
  let hQAbelianKan := inferInstanceAs (∀ F : X.left.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
    (etaleRestriction (Of.ι (CompDiagram.ofComposite X g D))).op.HasLeftKanExtension F)
  let hQKanCompose := inferInstanceAs ((forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
    (etaleRestriction (Of.ι (CompDiagram.ofComposite X g D))).op)
  @isoOfHom Z (Over.mk (X.hom ≫ g)) Λ inferInstance (CompDiagram.ofComposite X g C) (CompDiagram.ofComposite X g D) φ.homComposite
    hSourceSheafify hSourceOver hSourceDerived
    hPSheafify hPOver hPDerived hQSheafify hQOver hQDerived hTargetDerived
    hPModuleKan hQModuleKan hSourceCompose hPCompose hQCompose
    (inferInstanceAs (HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}))
    hPAbelian hQAbelian hPPreserves hQPreserves
    hPAbelianKan hQAbelianKan hPKanCompose hQKanCompose
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance

/-- Compatible diagram morphisms induce the horizontal composite of the two compactification
transitions on the iterated lower shriek models. -/
@[no_expose]
def domainTransition (φ : CompDiagram.DiagramHom X g C D) :
    compDomain X g D Λ ⟶ compDomain X g C Λ :=
  eqToHom (compDomain_def X g D Λ) ≫
    whiskerRight (diagramInteriorTransition X g C Λ D φ)
      ((etaleExtensionByZero (U := Y) (X := D.P_g.obj.right.left)
        (Of.ι D.P_g) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
          etaleDerivedPushforward D.P_g.obj.right.hom) ≫
    whiskerLeft
      ((etaleExtensionByZero (U := X.left) (X := CompDiagram.interior X g C)
        (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ)).mapDerivedCategory ⋙
          etaleDerivedPushforward (X := CompDiagram.interior X g C) (Y := Y)
            (CompDiagram.toBase X g C))
      (diagramBaseTransition X g C Λ D φ) ≫
    eqToHom (compDomain_def X g C Λ).symm

/-- Compatible diagram morphisms induce the compactification transition for the composite
morphism on the target lower shriek models. -/
@[no_expose]
def codomainTransition (φ : CompDiagram.DiagramHom X g C D) :
    compCodomain X g D Λ ⟶ compCodomain X g C Λ :=
  eqToHom (compCodomain_def X g D Λ) ≫
    diagramCompositeTransition X g C Λ D φ ≫
    eqToHom (compCodomain_def X g C Λ).symm

include h_X_compact h_X_quasiSeparated in
/-- The lower shriek composition comparison commutes with both compactification transitions
for every compatible diagram morphism. -/
theorem comp_naturality (φ : CompDiagram.DiagramHom X g C D) :
    comp X g D Λ ≫ codomainTransition X g C Λ D φ =
      domainTransition X g C Λ D φ ≫ comp X g C Λ := sorry

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

end
