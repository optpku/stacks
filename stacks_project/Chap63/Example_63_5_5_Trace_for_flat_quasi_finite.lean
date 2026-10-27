/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.FiberWeight
import StacksCheckRecall

/-!
# Trace for flat quasi-finite morphisms

Canonical positive fibre weights give functorial derived traces compatible
with arbitrary base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

/- Example 63.5.5 (Trace for flat quasi-finite) (1): The canonical fibre weight is the local closed-fibre
length times the finite inseparable residue-field degree. -/
@[stacks 0GKI] #check
  (AlgebraicGeometry.Scheme.Hom.fiberWeight_apply :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X),
      f.fiberWeight x =
        ((Module.length (X.presheaf.stalk x)
              ((X.presheaf.stalk x) ⧸
                (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map
                  (f.stalkMap x).hom)).toNat *
            Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℕ))

/- Example 63.5.5 (Trace for flat quasi-finite) (2): The canonical fibre weight is a positive weighting
for a flat, locally quasi-finite, locally finitely presented morphism. -/
@[stacks 0GKI] #check
  (AlgebraicGeometry.Scheme.Hom.fiberWeight_isPositiveWeighting :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f],
      f.IsWeighting f.fiberWeight ∧ ∀ x : X, 0 < f.fiberWeight x)

/- Example 63.5.5 (Trace for flat quasi-finite) (3): The canonical derived trace is a morphism
`f_! f⁻¹ K ⟶ K` for every derived étale sheaf of `Λ`-modules. -/
@[stacks 0GKI] #check
  (AlgebraicGeometry.Scheme.Etale.fiberWeightTraceDerivedHom :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f]
    [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    (Λ : Type u) [CommRing Λ]
    [X.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [Y.smallEtaleTopology.HasSheafCompose
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [Y.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [HasWeakSheafify X.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify Y.smallEtaleTopology (ModuleCat.{u} Λ)]
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
    [X.smallEtaleTopology.PreservesSheafification
      (forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u})]
    [∀ P : Y.Etaleᵒᵖ ⥤ ModuleCat.{u} Λ,
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
      (smallEtalePullback f).op.HasLeftKanExtension P]
    [(forget₂ (ModuleCat.{u} Λ) AddCommGrpCat.{u}).PreservesLeftKanExtensions
      (smallEtalePullback f).op]
    [∀ U : X.Etale,
      HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [∀ U : Y.Etale,
      HasWeakSheafify (Y.smallEtaleTopology.over U) (ModuleCat.{u} Λ)]
    [HasDerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u} Λ))]
    [HasDerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))]
    (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))),
    (lowerShriekModuleDerived f Λ).obj
      ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K)

section Derived

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f]
variable [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]

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

/- Example 63.5.5 (Trace for flat quasi-finite) (4): The derived trace is functorial in `K`. -/
@[stacks 0GKI] #check (AlgebraicGeometry.Scheme.Etale.fiberWeightTraceDerived_natural f Λ :
  ∀ {K L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))}
    (φ : K ⟶ L),
    (lowerShriekModuleDerived f Λ).map ((etaleModuleDerivedInverseImage f Λ).map φ) ≫
      fiberWeightTraceDerivedHom f Λ L = fiberWeightTraceDerivedHom f Λ K ≫ φ)

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

/- Example 63.5.5 (Trace for flat quasi-finite) (5): The derived trace commutes with arbitrary cartesian
base change and uses the canonical fibre weight of the new morphism. -/
@[stacks 0GKI] #check (AlgebraicGeometry.Scheme.Etale.fiberWeightTraceDerived_baseChange
    f Λ g f' g' h_cart :
  ∀ K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ)),
    (etaleModuleDerivedInverseImage g Λ).map (fiberWeightTraceDerivedHom f Λ K) =
      (weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart K).hom ≫
        fiberWeightTraceDerivedHom f' Λ ((etaleModuleDerivedInverseImage g Λ).obj K))

end Derived

/- Example 63.5.5 (Trace for flat quasi-finite) (6): Flatness is preserved by arbitrary base change. -/
@[stacks 0GKI] #check (CategoryTheory.MorphismProperty.of_isPullback (P := @Flat) :
  ∀ {Y' X X' Y : Scheme.{u}} {g : Y' ⟶ Y} {f : X ⟶ Y}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'},
    IsPullback g' f' f g → Flat f → Flat f')

/- Example 63.5.5 (Trace for flat quasi-finite) (7): Local quasi-finiteness is preserved by arbitrary base change. -/
@[stacks 0GKI] #check (CategoryTheory.MorphismProperty.of_isPullback (P := @LocallyQuasiFinite) :
  ∀ {Y' X X' Y : Scheme.{u}} {g : Y' ⟶ Y} {f : X ⟶ Y}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'},
    IsPullback g' f' f g → LocallyQuasiFinite f → LocallyQuasiFinite f')

/- Example 63.5.5 (Trace for flat quasi-finite) (8): Local finite presentation is preserved by arbitrary base change. -/
@[stacks 0GKI] #check (CategoryTheory.MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) :
  ∀ {Y' X X' Y : Scheme.{u}} {g : Y' ⟶ Y} {f : X ⟶ Y}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'},
    IsPullback g' f' f g → LocallyOfFinitePresentation f → LocallyOfFinitePresentation f')

/- Example 63.5.5 (Trace for flat quasi-finite) (9): The canonical fibre weight restricts to the canonical
weighting of the base change. -/
@[stacks 0GKI] #check
  (AlgebraicGeometry.Scheme.Hom.fiberWeight_isPullback :
    ∀ {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
      (f' : X' ⟶ Y') (g' : X' ⟶ X)
      [Flat f] [LocallyQuasiFinite f] [LocallyOfFinitePresentation f]
      [Flat f'] [LocallyQuasiFinite f'] [LocallyOfFinitePresentation f'],
      IsPullback g' f' f g →
        (fun x' : X' ↦ f.fiberWeight (g' x')) = f'.fiberWeight)

end
