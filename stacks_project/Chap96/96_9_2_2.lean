/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafComparison
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.SheafRestriction

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

variable {S : Scheme.{u}} {X : GroupoidsOver S}
variable {x y : X.total} (φ : x ⟶ y) (F : Sheaf X.etaleTopology (Type (u + 1)))
variable [HasWeakSheafify (X.p.obj x).left.smallEtaleTopology (Type (u + 1))]
variable [∀ P : (X.p.obj y).left.Etaleᵒᵖ ⥤ Type (u + 1),
    (Scheme.smallEtalePullback (X.p.map φ).left).op.HasLeftKanExtension P]

/- 96.9.2.2 Let φ : x ⟶ y be a morphism of a category fibred in groupoids X over
(Sch/S)_fppf lying over a : U ⟶ V, and let F be an étale sheaf on X. The
comparison morphism comparison φ F is the adjunct
a_small⁻¹(F|_{V_étale}) ⟶ F|_{U_étale} of comparisonPush φ F.obj, obtained via
(smallEtalePullback a).sheafAdjunctionContinuous.homEquiv.symm of
ObjectProperty.homMk (comparisonPush φ F.obj). -/
@[stacks 06W3]
#check (AlgebraicGeometry.GroupoidsOver.comparison φ F :
    ((Scheme.smallEtalePullback (X.p.map φ).left).sheafPullback (Type (u + 1))
        (X.p.obj y).left.smallEtaleTopology
        (X.p.obj x).left.smallEtaleTopology).obj
      (GroupoidsOver.restrictSmallEtaleSheaf F y) ⟶
    GroupoidsOver.restrictSmallEtaleSheaf F x)
