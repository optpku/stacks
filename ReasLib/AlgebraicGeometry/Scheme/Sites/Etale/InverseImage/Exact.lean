/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Sites.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Inverse image of abelian sheaves on small étale sites preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits_addCommGrp
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{w}
        Y.smallEtaleTopology X.smallEtaleTopology) := sorry

/-- Inverse image of abelian sheaves on small étale sites is exact. -/
theorem smallEtaleInverseImage_exact_addCommGrp
    [HasWeakSheafify X.smallEtaleTopology AddCommGrpCat.{w}]
    [∀ P : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{w},
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    exactFunctor _ _
      ((smallEtalePullback f).sheafPullback AddCommGrpCat.{w}
        Y.smallEtaleTopology X.smallEtaleTopology) := sorry

/-- Inverse image of set-valued sheaves on small étale sites preserves finite limits. -/
instance smallEtaleInverseImage_preservesFiniteLimits_type
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [∀ P : Y.Etaleᵒᵖ ⥤ Type v,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    PreservesFiniteLimits
      ((smallEtalePullback f).sheafPullback (Type v)
        Y.smallEtaleTopology X.smallEtaleTopology) := sorry

/-- Inverse image of set-valued sheaves on small étale sites preserves finite limits
and finite colimits. -/
theorem smallEtaleInverseImage_exact_type
    [HasWeakSheafify X.smallEtaleTopology (Type v)]
    [∀ P : Y.Etaleᵒᵖ ⥤ Type v,
      (smallEtalePullback f).op.HasLeftKanExtension P] :
    exactFunctor _ _
      ((smallEtalePullback f).sheafPullback (Type v)
        Y.smallEtaleTopology X.smallEtaleTopology) := sorry

end AlgebraicGeometry.Scheme
