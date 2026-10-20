/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.FiberLength
public import stacks_project.Chap63.Lemma_63_5_3

/-!
# Canonical traces for flat locally quasi-finite morphisms

Specializations of the weighting traces of Lemmas 63.5.2 and 63.5.3 at the
canonical fibre-weight weighting of a flat, locally quasi-finite, locally
finitely presented scheme morphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

/-- The sheaf-level trace obtained from the canonical fibre-weight weighting of
a flat, locally quasi-finite, locally finitely presented morphism. -/
def fiberWeightTraceHom (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (lowerShriek f).obj ((etaleAbelianSheafPullback f).obj F) ⟶ F :=
  weightingTrace f (fiberWeight_isPositiveWeighting f).1 F

/-- The sheaf-level fibre-weight trace is the weighting trace at
`f.fiberWeight`. -/
theorem fiberWeightTraceHom_eq
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    fiberWeightTraceHom f F =
      weightingTrace f (fiberWeight_isPositiveWeighting f).1 F :=
  sorry

section Derived

variable (Λ : Type u) [CommRing Λ]
variable [X.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [Y.smallEtaleTopology.HasSheafCompose
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [Y.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
variable [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [X.smallEtaleTopology.PreservesSheafification
  (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
variable [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
  (smallEtalePullback f).op.HasLeftKanExtension P]
variable [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
  (smallEtalePullback f).op]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [∀ U : Y.Etale,
  HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
variable [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
variable [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]

/-- Derived natural transformation of fibre-weight traces, obtained by
specializing `weightingTraceDerivedNatTrans` at `f.fiberWeight`. -/
def fiberWeightTraceDerivedNatTrans :
    etaleModuleDerivedInverseImage f Λ ⋙ lowerShriekModuleDerived f Λ ⟶
      𝟭 (EtaleDerived Y Λ) :=
  weightingTraceDerivedNatTrans f Λ (fiberWeight_isPositiveWeighting f).1

/-- Objectwise derived trace `Tr_{f, K}` for the canonical fibre-weight
weighting. -/
def fiberWeightTraceDerivedHom (K : EtaleDerived Y Λ) :
    (lowerShriekModuleDerived f Λ).obj
        ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K :=
  weightingTraceDerived f Λ (fiberWeight_isPositiveWeighting f).1 K

/-- The objectwise derived fibre-weight trace is the weighting trace at
`f.fiberWeight`. -/
theorem fiberWeightTraceDerivedHom_eq (K : EtaleDerived Y Λ) :
    fiberWeightTraceDerivedHom f Λ K =
      weightingTraceDerived f Λ (fiberWeight_isPositiveWeighting f).1 K :=
  sorry

/-- Functoriality of the derived fibre-weight trace in `K`. -/
theorem fiberWeightTraceDerived_natural {K L : EtaleDerived Y Λ} (φ : K ⟶ L) :
    (lowerShriekModuleDerived f Λ).map
          ((etaleModuleDerivedInverseImage f Λ).map φ) ≫
        fiberWeightTraceDerivedHom f Λ L =
      fiberWeightTraceDerivedHom f Λ K ≫ φ :=
  sorry

section DerivedBaseChange

variable {X' Y' : Scheme.{u}} (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable [Flat f'] [LocallyQuasiFinite f'] [LocallyOfFinitePresentation f']
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

/-- Derived fibre-weight traces are compatible with cartesian base change, using
the canonical fibre-weight trace of `f'` rather than the restricted weighting
`f.fiberWeight ∘ g'`. -/
theorem fiberWeightTraceDerived_baseChange (K : EtaleDerived Y Λ) :
    (etaleModuleDerivedInverseImage g Λ).map
        (fiberWeightTraceDerivedHom f Λ K) =
      (weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart K).hom ≫
        fiberWeightTraceDerivedHom f' Λ
          ((etaleModuleDerivedInverseImage g Λ).obj K) :=
  sorry

end DerivedBaseChange

end Derived

end AlgebraicGeometry.Scheme.Etale

end
