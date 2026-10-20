/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsWithSupport
public import stacks_project.Chap59.Lemma_59_79_1_DirectImage

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.79.1 (09XQ): for a closed immersion `i : Z ⟶ X`, the sheaf of sections
with support in `Z` sends injective abelian sheaves on `X.smallEtaleTopology` to injective
abelian sheaves on `Z.smallEtaleTopology`. -/
@[stacks 09XQ]
#check (AlgebraicGeometry.Scheme.Etale.sectionsWithSupport_injective :
  ∀ {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}) [Injective F],
    Injective ((AlgebraicGeometry.Scheme.Etale.sectionsWithSupport i).obj F))
