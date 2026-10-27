/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Module
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.LocallyQuasiFinite
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Composition
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Identity

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] [LocallyOfFiniteType f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

variable (Λ : Type u) [Ring Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]

variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived natural transformation of the weighting trace, obtained by
`ExactFunctor.MapDerivedCategory.map` of the sheaf-level module trace and
reassociating the composite `f_! ∘ f⁻¹`. -/
def weightingTraceDerivedNatTrans {w : X → ℤ} (hw : f.IsWeighting w) :
    etaleModuleDerivedInverseImage f Λ ⋙ lowerShriekModuleDerived f Λ ⟶
      𝟭 (DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :=
  (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))
        (ExactFunctor.of (lowerShriekModule f Λ))).inv ≫
    ExactFunctor.MapDerivedCategory.map
      (ObjectProperty.homMk (weightingTraceModuleNatTrans f Λ hw) :
        (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ))).comp
            (ExactFunctor.of (lowerShriekModule f Λ)) ⟶
          ExactFunctor.id (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) ≫
    (ExactFunctor.MapDerivedCategory.idFunctorIso
      (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))).hom

/-- Objectwise derived weighting trace `Tr_{f, w, K} : f_! f⁻¹ K ⟶ K`. -/
def weightingTraceDerived {w : X → ℤ} (hw : f.IsWeighting w)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (lowerShriekModuleDerived f Λ).obj
        ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K :=
  (weightingTraceDerivedNatTrans f Λ hw).app K

/-- Functoriality of the derived weighting trace in `K`. -/
theorem weightingTraceDerived_natural {w : X → ℤ} (hw : f.IsWeighting w)
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))} (φ : K ⟶ L) :
    (lowerShriekModuleDerived f Λ).map
          ((etaleModuleDerivedInverseImage f Λ).map φ) ≫
        weightingTraceDerived f Λ hw L =
      weightingTraceDerived f Λ hw K ≫ φ := sorry

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [LocallyQuasiFinite f'] [LocallyOfFiniteType f']
variable [HasSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [X'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y'.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasWeakSheafify X'.smallEtaleTopology AddCommGrpCat.{u}]
variable [Y'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [X'.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (f' ≫ g)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback (g' ≫ f)).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g).op.HasLeftKanExtension P]
variable [∀ P : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback g').op.HasLeftKanExtension P]
variable [∀ P : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f').op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g).op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback g').op]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f').op]
variable [∀ U : X'.Etale,
  HasWeakSheafify (X'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y'.Etale,
  HasWeakSheafify (Y'.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X'.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived left-vertical identification of the weighting-trace base-change
square, obtained by `ExactFunctor.MapDerivedCategory` of the sheaf-level
module identification after reassociating composites of exact functors. -/
def weightingTraceDerivedBaseChangeIso (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage g Λ).obj
        ((lowerShriekModuleDerived f Λ).obj
          ((etaleModuleDerivedInverseImage f Λ).obj K)) ≅
      (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage f' Λ).obj
          ((etaleModuleDerivedInverseImage g Λ).obj K)) :=
  (etaleModuleDerivedInverseImage g Λ).mapIso
      ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ)))
          (ExactFunctor.of (lowerShriekModule f Λ))).symm.app K) ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (Sheaf.smallEtaleInverseImage f (ModuleCat.{u} Λ) ⋙ lowerShriekModule f Λ))
        (ExactFunctor.of (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))).symm.app K ≪≫
    Functor.MapDerivedCategory.objIso
      (weightingTraceModuleBaseChangeNatIso f Λ g f' g' h_cart) K ≪≫
    (ExactFunctor.MapDerivedCategory.compFunctorIso
        (ExactFunctor.of
          (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ) ⋙ Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ)))
        (ExactFunctor.of (lowerShriekModule f' Λ))).app K ≪≫
    (lowerShriekModuleDerived f' Λ).mapIso
      ((ExactFunctor.MapDerivedCategory.compFunctorIso
          (ExactFunctor.of (Sheaf.smallEtaleInverseImage g (ModuleCat.{u} Λ)))
          (ExactFunctor.of (Sheaf.smallEtaleInverseImage f' (ModuleCat.{u} Λ)))).app K)

/-- The derived weighting trace on a cartesian base change, for the
pulled-back weighting `w ∘ g'`. -/
def weightingTraceDerived_isPullback {w : X → ℤ} (hw : f.IsWeighting w)
    (K : DerivedCategory (Sheaf Y'.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (lowerShriekModuleDerived f' Λ).obj
        ((etaleModuleDerivedInverseImage f' Λ).obj K) ⟶ K :=
  weightingTraceDerived f' Λ (w := fun x' ↦ w (g' x'))
    (IsWeighting.of_isPullback hw h_cart) K

/-- Derived weighting traces are compatible with arbitrary cartesian base
change: `g⁻¹ Tr_{f, w, K} = iso.hom ≫ Tr_{f', w ∘ g', g⁻¹ K}`. -/
theorem weightingTraceDerived_baseChange {w : X → ℤ} (hw : f.IsWeighting w)
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))) :
    (etaleModuleDerivedInverseImage g Λ).map
        (weightingTraceDerived f Λ hw K) =
      (weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart K).hom ≫
        weightingTraceDerived_isPullback f Λ g f' g' h_cart hw
          ((etaleModuleDerivedInverseImage g Λ).obj K) := sorry

end AlgebraicGeometry.Scheme.Etale

end
