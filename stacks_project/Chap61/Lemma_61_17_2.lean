module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.IsomorphismClasses
public import ReasLib.CategoryTheory.Sites.Over.Derived.BaseChange
public import stacks_project.Chap61.Lemma_61_17_2_Derived
public import stacks_project.Chap61.Lemma_61_17_2_Pushforward
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 61.17.2

Restriction of `Rf_big,*` to a small pro-étale site agrees with `Rf_small,*`
of the restriction, and the same comparison holds after cartesian base change
on both the small and the big sites.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Derived.Over

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/-- Lemma 61.17.2 (1): for `f : T ⟶ S` and `K` in `D((Sch/T)_proétale)`, the
restriction of `Rf_big,* K` to `S_proétale` agrees with `Rf_small,*` of the
restriction of `K`. -/
@[stacks 0F68]
theorem restrict_bigDerivedPushforward {S T : Scheme.{u}} (f : T ⟶ S)
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (topology T) AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [(iInverseImage (𝟙 S)).Additive]
    [PreservesFiniteLimits (iInverseImage (𝟙 S))]
    [PreservesFiniteColimits (iInverseImage (𝟙 S))]
    [(iInverseImage (𝟙 T)).Additive]
    [PreservesFiniteLimits (iInverseImage (𝟙 T))]
    [PreservesFiniteColimits (iInverseImage (𝟙 T))]
    (K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((iInverseImage (𝟙 S)).mapDerivedCategory.obj
        ((bigDerivedPushforward f).obj K))
      ((smallDerivedPushforward f).obj
        ((iInverseImage (𝟙 T)).mapDerivedCategory.obj K)) := sorry

/-- Lemma 61.17.2 (2): for a cartesian square and `K` in `D((Sch/T)_proétale)`,
`iInverseImage g` of `Rf_big,* K` agrees with `Rf'_small,*` of
`iInverseImage g' K` in `D(S'_proétale)`. -/
@[stacks 0F68]
theorem iInverseImage_bigDerivedPushforward
    {S T S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g)
    [HasSheafify (topology S') AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T') AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [IsGrothendieckAbelian (Sheaf (topology S') AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (topology T') AddCommGrpCat.{u + 1})]
    [IsGrothendieckAbelian (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [(iInverseImage g).Additive]
    [PreservesFiniteLimits (iInverseImage g)]
    [PreservesFiniteColimits (iInverseImage g)]
    [(iInverseImage g').Additive]
    [PreservesFiniteLimits (iInverseImage g')]
    [PreservesFiniteColimits (iInverseImage g')]
    (K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})) :
    IsIsomorphic
      ((iInverseImage g).mapDerivedCategory.obj
        ((bigDerivedPushforward f).obj K))
      ((smallDerivedPushforward f').obj
        ((iInverseImage g').mapDerivedCategory.obj K)) := sorry

/-- Lemma 61.17.2 (3): for a cartesian square and `K` in `D((Sch/T)_proétale)`,
`g_big⁻¹ (Rf_big,* K)` agrees with `Rf'_big,* ((g'_big)⁻¹ K)` in
`D((Sch/S')_proétale)`. -/
@[stacks 0F68]
theorem bigInverseImage_bigDerivedPushforward
    {S T S' T' : Scheme.{u}} (f : T ⟶ S) (g : S' ⟶ S) (f' : T' ⟶ S') (g' : T' ⟶ T)
    (sq : IsPullback g' f' f g)
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S') AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over T') AddCommGrpCat.{u + 1}]
    [∀ P : (Over T)ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f).op.HasPointwiseRightKanExtension P]
    [∀ P : (Over T')ᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (Over.map f').op.HasPointwiseRightKanExtension P]
    (K : DerivedCategory (Sheaf (proetaleTopology.over T) AddCommGrpCat.{u + 1})) :
    IsIso ((BaseChange.map proetaleTopology g' f' f g sq.w).app K) := sorry

end AlgebraicGeometry.Scheme.ProEt
