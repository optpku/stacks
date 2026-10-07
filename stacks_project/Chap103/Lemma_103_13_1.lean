module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import stacks_project.Chap96.Definition_96_4_1_AssociatedTopology
public import stacks_project.Chap100.Definition_100_6_1_QuasiCompact
public import stacks_project.Chap101.Definition_101_8_1_Noetherian

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

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 103.13.1 (1): Let `X` be a quasi-compact and quasi-separated algebraic
stack. Then for every filtered diagram `ℱ` of abelian sheaves on `X` in the
fppf topology and every `p : ℕ`, the canonical map
`colimit.post ℱ (Sheaf.functorH X.fppfTopology p)` is an isomorphism. -/
@[stacks 0GQV]
instance functorH_fppf_colimitComparison_isIso
    {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify X.fppfTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.fppfTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.fppfTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.functorH X.fppfTopology p)] :
    IsIso (colimit.post ℱ (Sheaf.functorH X.fppfTopology p)) :=
  sorry

/-- Lemma 103.13.1 (2): Let `X` be a quasi-compact and quasi-separated algebraic
stack. Then for every filtered diagram `ℱ` of abelian sheaves on `X_étale` and
every `p : ℕ`, the canonical map
`colimit.post ℱ (Sheaf.functorH X.etaleTopology p)` is an isomorphism. -/
@[stacks 0GQV]
instance functorH_etale_colimitComparison_isIso
    {S : Scheme.{u}} {X : GroupoidsOver S}
    [AlgebraicStack X] [IsQuasiCompact X] [IsQuasiSeparated X]
    [HasSheafify X.etaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf X.etaleTopology AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf X.etaleTopology AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.functorH X.etaleTopology p)] :
    IsIso (colimit.post ℱ (Sheaf.functorH X.etaleTopology p)) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
