module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap69.Definition_69_6_2_ExtensionByZero

/-!
# Lemma 69.5.1

Filtered colimits of abelian étale sheaves commute with cohomology on a
quasi-compact quasi-separated algebraic space.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 69.5.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `X` is quasi-compact and quasi-separated, then for every filtered diagram
`ℱ` of abelian sheaves on `X_étale` and every `p : ℕ`, the canonical map
`colimit.post ℱ (Sheaf.functorH (smallEtaleTopology X) p)` is an isomorphism. -/
@[stacks 073E]
instance functorH_colimitComparison_isIso
    {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.functorH (smallEtaleTopology X) p)] :
    IsIso (colimit.post ℱ (Sheaf.functorH (smallEtaleTopology X) p)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
