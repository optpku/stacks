/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Cohomology.FilteredColimit
import StacksCheckRecall

/-!
# Lemma 103.13.1

Filtered colimits of abelian sheaves commute with cohomology on a
quasi-compact quasi-separated algebraic stack, both on the associated fppf
site and on the associated étale site.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

/- Lemma 103.13.1 (1): Filtered colimits commute with fppf cohomology of a
quasi-compact quasi-separated algebraic stack. -/
@[stacks 0GQV]
#check (AlgebraicGeometry.AlgebraicStack.functorH_fppf_colimitComparison_isIso :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify X.fppfTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.fppfTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.fppfTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.functorH X.fppfTopology p)],
    IsIso (colimit.post ℱ (Sheaf.functorH X.fppfTopology p)))

/- Lemma 103.13.1 (2): Filtered colimits commute with étale cohomology of a
quasi-compact quasi-separated algebraic stack. -/
@[stacks 0GQV]
#check (AlgebraicGeometry.AlgebraicStack.functorH_etale_colimitComparison_isIso :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.etaleTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.functorH X.etaleTopology p)],
    IsIso (colimit.post ℱ (Sheaf.functorH X.etaleTopology p)))
