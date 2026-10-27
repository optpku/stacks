/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.HigherDirectImage.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 103.13.2

Filtered colimits of abelian sheaves commute with higher direct images along a
quasi-compact quasi-separated morphism of algebraic stacks, both in the fppf
topology and in the étale topology.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicStack GroupoidsOver
open scoped Bicategory

noncomputable section

universe u

/- Lemma 103.13.2 (1): Filtered colimits commute with higher direct images
along a quasi-compact quasi-separated morphism of algebraic stacks in the fppf topology. -/
@[stacks 0GQW]
#check (AlgebraicGeometry.AlgebraicStack.higherDirectImageFunctor_fppf_colimitComparison_isIso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [AlgebraicStack X] [AlgebraicStack Y] [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.fppfTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.fppfTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf X.fppfTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.fppfTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ higherDirectImageFunctor f StandardTopology.fppf p)],
    IsIso (colimit.post ℱ (higherDirectImageFunctor f StandardTopology.fppf p)))

/- Lemma 103.13.2 (2): Filtered colimits commute with higher direct images
along a quasi-compact quasi-separated morphism of algebraic stacks in the étale topology. -/
@[stacks 0GQW]
#check (AlgebraicGeometry.AlgebraicStack.higherDirectImageFunctor_etale_colimitComparison_isIso :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} (f : X ⟶ Y)
    [AlgebraicStack X] [AlgebraicStack Y] [QuasiCompact f] [QuasiSeparated f]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u + 1}]
    [HasSheafify Y.etaleTopology AddCommGrpCat.{u + 1}]
    [HasInjectiveResolutions (Sheaf X.etaleTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.etaleTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ higherDirectImageFunctor f StandardTopology.etale p)],
    IsIso (colimit.post ℱ (higherDirectImageFunctor f StandardTopology.etale p)))
