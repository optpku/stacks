/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.Pullback
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Derived
public import stacks_project.Chap61.Lemma_61_12_19_Pullback
public import stacks_project.Chap61.Lemma_61_17_1_InverseImage

/-!
# Abelian inverse image along small pro-étale pullback

This leaf owns the abelian sheaf functor `f_small⁻¹` induced by
`smallProetalePullback`, together with exactness instances for that functor
and for relocalization inverse image `iInverseImage`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ProEt

variable {S T : Scheme.{u}} (f : T ⟶ S)

/-- Inverse image on abelian sheaves along small pro-étale base change `f_small`. -/
abbrev smallInverseImage
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    Sheaf (topology S) AddCommGrpCat.{u + 1} ⥤
      Sheaf (topology T) AddCommGrpCat.{u + 1} :=
  (smallProetalePullback f).sheafPullback AddCommGrpCat.{u + 1}
    (topology S) (topology T)

/-- Inverse image `f_small⁻¹` is sheaf pullback along `smallProetalePullback`. -/
theorem smallInverseImage_eq
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    smallInverseImage f =
      (smallProetalePullback f).sheafPullback AddCommGrpCat.{u + 1}
        (topology S) (topology T) := sorry

/-- Inverse image `f_small⁻¹` on abelian sheaves preserves finite limits. -/
instance smallInverseImage_preservesFiniteLimits
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteLimits (smallInverseImage f) := sorry

/-- Inverse image `f_small⁻¹` on abelian sheaves preserves finite colimits. -/
instance smallInverseImage_preservesFiniteColimits
    [HasSheafify (topology S) AddCommGrpCat.{u + 1}]
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [∀ P : S.ProEtᵒᵖ ⥤ AddCommGrpCat.{u + 1},
      (smallProetalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteColimits (smallInverseImage f) := sorry

/-- Inverse image `iInverseImage f` on abelian sheaves preserves finite limits. -/
instance iInverseImage_preservesFiniteLimits
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}] :
    PreservesFiniteLimits (iInverseImage f) := sorry

/-- Inverse image `iInverseImage f` on abelian sheaves preserves finite colimits. -/
instance iInverseImage_preservesFiniteColimits
    [HasSheafify (topology T) AddCommGrpCat.{u + 1}]
    [HasSheafify (proetaleTopology.over S) AddCommGrpCat.{u + 1}] :
    PreservesFiniteColimits (iInverseImage f) := sorry

end AlgebraicGeometry.Scheme.ProEt
