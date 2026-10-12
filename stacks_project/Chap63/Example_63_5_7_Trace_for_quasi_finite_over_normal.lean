/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting.GenericSeparableDegree
import stacks_project.Chap63.Lemma_63_5_3

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Etale

universe u

/- Example 63.5.7 (Trace for quasi-finite over normal) (1): if `Y` is
geometrically unibranch and locally Noetherian, for example a normal variety,
and `f : X ⟶ Y` is locally quasi-finite, Lemma 37.75.8 supplies a nonnegative
weighting `w : X → ℕ` given pointwise by generic separable degrees on stalks. -/
@[stacks 0GKJ] #check
  (exists_genericSepDegreeWeighting :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyOfFiniteType f] [LocallyQuasiFinite f] [IsLocallyNoetherian Y],
      Y.isGeometricallyUnibranch →
        ∃ w : X → ℕ, f.IsWeighting (fun x ↦ (w x : ℤ)) ∧
          ∀ x : X, RingHom.IsGenericSepDegree (f.stalkMap x).hom
            (LocallyOfFiniteType.stalkMap f x) (f.quasiFiniteAt x) (w x))

/- Example 63.5.7 (Trace for quasi-finite over normal) (2): Lemmas 63.5.2 and
63.5.3 then give derived traces `Tr_{f, w, K} : f_! f⁻¹ K ⟶ K` on
`D(Y_étale, Λ)`, functorial in `K` by `weightingTraceDerived_natural` and
compatible with arbitrary cartesian base change by
`weightingTraceDerived_baseChange`. -/
@[stacks 0GKJ] #check
  (weightingTraceDerived :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
      [LocallyQuasiFinite f] [LocallyOfFiniteType f]
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
      {w : X → ℤ}, f.IsWeighting w → ∀ (K : EtaleDerived Y Λ),
      (lowerShriekModuleDerived f Λ).obj
          ((etaleModuleDerivedInverseImage f Λ).obj K) ⟶ K)

/- Example 63.5.7 (Trace for quasi-finite over normal) (3): restriction of `w`
along a cartesian square remains a weighting of the base change `f'`, but
`w ∘ g'` is not in general the generic-separable-degree weighting of `f'`. -/
@[stacks 0GKJ] #check
  (IsWeighting.of_isPullback :
    ∀ {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} [LocallyQuasiFinite f]
      {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {w : X → ℤ},
      f.IsWeighting w → ∀ [LocallyQuasiFinite f'],
        IsPullback g' f' f g → f'.IsWeighting (fun x' ↦ w (g' x')))

end
