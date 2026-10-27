/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.GenericSeparableDegree
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Trace.Weighting.Derived

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

universe u

/- The example says “positive”, whereas its cited Lemma 37.75.8 explicitly
constructs a nonnegative weighting. The check below retains that construction;
strict positivity does not hold under the stated hypotheses. -/

/- Example 63.5.7 (Trace for quasi-finite over normal) (1): if `Y` is
geometrically unibranch and locally Noetherian, for example a normal variety,
and `f : X ⟶ Y` is locally quasi-finite, Lemma 37.75.8 supplies a nonnegative
weighting `w : X → ℕ` given pointwise by generic separable degrees on stalks. -/
@[stacks 0GKJ] #check
  (AlgebraicGeometry.Scheme.Hom.exists_genericSepDegreeWeighting :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian Y],
      Y.isGeometricallyUnibranch →
        ∃ w : X → ℕ, f.IsWeighting (fun x ↦ (w x : ℤ)) ∧
          ∀ x : X, RingHom.IsGenericSepDegree (f.stalkMap x).hom
            (LocallyOfFiniteType.stalkMap f x) (f.quasiFiniteAt x) (w x))

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable [LocallyQuasiFinite f] [LocallyOfFiniteType f]
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

/- Example 63.5.7 (Trace for quasi-finite over normal) (2): Lemmas 63.5.2 and
63.5.3 then give derived traces `Tr_{f, w, K} : f_! f⁻¹ K ⟶ K` on
`D(Y_étale, Λ)`, functorial in `K` by `weightingTraceDerived_natural` and
compatible with arbitrary cartesian base change by
`weightingTraceDerived_baseChange`. -/
@[stacks 0GKJ] #check
  (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived f Λ :
    ∀ {w : X → ℤ}, f.IsWeighting w →
      ∀ (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))),
      (lowerShriekModuleDerived f Λ).obj
          ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K)

#check (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived_natural f Λ :
  ∀ {w : X → ℤ} (hw : f.IsWeighting w)
    {K L : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))} (φ : K ⟶ L),
    (lowerShriekModuleDerived f Λ).map
          ((etaleModuleDerivedInverseImage f Λ).map φ) ≫
        weightingTraceDerived f Λ hw L =
      weightingTraceDerived f Λ hw K ≫ φ)

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

/- Example 63.5.7 (Trace for quasi-finite over normal) (3): the trace commutes
with arbitrary cartesian base change for the restricted weighting `w ∘ g'`.
This remains a weighting of `f'`, but need not have an intrinsic interpretation
as the generic-separable-degree weighting of `f'`. -/
@[stacks 0GKJ] #check
  (AlgebraicGeometry.Scheme.Etale.weightingTraceDerived_baseChange f Λ g f' g' h_cart :
    ∀ {w : X → ℤ} (hw : f.IsWeighting w)
      (K : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u} Λ))),
      (etaleModuleDerivedInverseImage g Λ).map
          (weightingTraceDerived f Λ hw K) =
        (weightingTraceDerivedBaseChangeIso f Λ g f' g' h_cart K).hom ≫
          weightingTraceDerived_isPullback f Λ g f' g' h_cart hw
            ((etaleModuleDerivedInverseImage g Λ).obj K))

end

#check
  (AlgebraicGeometry.Scheme.Hom.IsWeighting.of_isPullback :
    ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f]
      {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {w : X → ℤ},
      f.IsWeighting w → ∀ [LocallyQuasiFinite f'],
        IsPullback g' f' f g → f'.IsWeighting (fun x' ↦ w (g' x')))

end
