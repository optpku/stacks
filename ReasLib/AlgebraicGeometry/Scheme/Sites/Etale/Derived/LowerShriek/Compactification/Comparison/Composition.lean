/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Comparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LowerShriek.Compactification.Composition

/-!
# Compatibility of the compactification comparison with composition
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open CategoryTheory.Functor.RightDerived CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Compactification

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

variable {Y Z : Scheme.{u}} (X : Over Y) (g : Y ⟶ Z)
  [IsSeparated X.hom] [Scheme.Hom.FiniteType X.hom]
  [IsSeparated g] [Scheme.Hom.FiniteType g]
  [CompactSpace X.left] [QuasiSeparatedSpace X.left]
  [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace Z] [QuasiSeparatedSpace Z]
  (C : CompDiagram X g)
  (Λ : Type u) [CommRing Λ]
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
  [(etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C))
    (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
    (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (Of.ι (CompDiagram.ofInterior X g C)) (ModuleCat.{u} Λ))]
  [(etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ)).Additive]
  [PreservesFiniteLimits
    (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ))]
  [PreservesFiniteColimits
    (etaleExtensionByZero (Of.ι C.P_g) (ModuleCat.{u} Λ))]
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

/-- Whiskered `toPushforward` from `Rf_! ⋙ Rg_!` to `Rf_* ⋙ Rg_*`. -/
irreducible_def toPushforward_compDomain :
    compDomain X g C Λ ⟶
      ((etaleDerivedPushforward X.hom :
          DerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ⋙
        (etaleDerivedPushforward g :
          DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)) ⥤ DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u} Λ)))) := by
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify (CompDiagram.interior X g C).smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `∀ U : (CompDiagram.interior X g C).Etale, HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale, HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.ofInterior X g C).obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.ofInterior X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify ((CompDiagram.interior X g C).smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk g).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `∀ U : Y.Etale, HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk g).left.Etale, HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk g).left.Etale,
      HasWeakSheafify ((Over.mk g).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  exact eqToHom (compDomain_def X g C Λ) ≫
    whiskerRight
      (toPushforward (Λ := Λ) X (CompDiagram.ofInterior X g C))
      (etaleDerivedLowerShriek (Λ := Λ) (Over.mk g) C.P_g) ≫
    whiskerLeft (etaleDerivedPushforward X.hom)
      (toPushforward (Λ := Λ) (Over.mk g) C.P_g)

/-- `toPushforward` from `R(g ∘ f)_!` to `R(g ∘ f)_*`. -/
irreducible_def toPushforward_compCodomain :
    compCodomain X g C Λ ⟶ etaleDerivedPushforward (X.hom ≫ g) := by
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf X.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (Over.mk (X.hom ≫ g)).left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify X.left.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `∀ U : X.left.Etale, HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (Over.mk (X.hom ≫ g)).left.Etale, HasWeakSheafify ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (Over.mk (X.hom ≫ g)).left.Etale,
      HasWeakSheafify ((Over.mk (X.hom ≫ g)).left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (X.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `HasDerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))` at definitionally identical `HasDerivedCategory (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))`; retain the supplied data under projection reduction.
  letI : HasDerivedCategory (Sheaf (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)) :=
    inferInstanceAs (HasDerivedCategory (Sheaf C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)))
  -- Local instance justification (defeq pin): Use supplied `HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)` at definitionally identical `HasSheafify (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : HasSheafify (CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ) :=
    inferInstanceAs (HasSheafify C.P_bar.obj.right.left.smallEtaleTopology (ModuleCat.{u} Λ))
  -- Local instance justification (defeq pin): Use supplied `∀ U : C.P_bar.obj.right.left.Etale, HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)` at definitionally identical `∀ U : (CompDiagram.ofComposite X g C).obj.right.left.Etale, HasWeakSheafify ((CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ)`; retain the supplied data under projection reduction.
  letI : ∀ U : (CompDiagram.ofComposite X g C).obj.right.left.Etale,
      HasWeakSheafify ((CompDiagram.ofComposite X g C).obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ) :=
    fun U => inferInstanceAs
      (HasWeakSheafify (C.P_bar.obj.right.left.smallEtaleTopology.over U) (ModuleCat.{u} Λ))
  exact eqToHom (compCodomain_def X g C Λ) ≫
    toPushforward (Λ := Λ) (Over.mk (X.hom ≫ g)) (CompDiagram.ofComposite X g C)

/-- Compatibility of `toPushforward` with `Rg_! ∘ Rf_! ⟶ R(g ∘ f)_!` and
`Rg_* ∘ Rf_* ⟶ R(g ∘ f)_*`. -/
theorem toPushforward_comp_compat :
    toPushforward_compDomain X g C Λ ≫
        (asIso (etaleDerivedPushforwardComp X.hom g Λ)).inv =
      comp X g C Λ ≫ toPushforward_compCodomain X g C Λ :=
  sorry

end AlgebraicGeometry.Scheme.Etale.etaleDerivedLowerShriek

end
