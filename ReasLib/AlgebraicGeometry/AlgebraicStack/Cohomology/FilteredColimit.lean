module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated

/-!
# Filtered colimits and cohomology of algebraic stacks

Filtered colimits of abelian sheaves commute with cohomology on a
quasi-compact quasi-separated algebraic stack in the fppf and étale topologies.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack AlgebraicGeometry.GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a quasi-compact quasi-separated algebraic stack, the canonical map
from the filtered colimit of degree-`p` fppf cohomology groups to the
degree-`p` fppf cohomology of the colimit abelian sheaf is an isomorphism. -/
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

/-- For a quasi-compact quasi-separated algebraic stack, the canonical map
from the filtered colimit of degree-`p` étale cohomology groups to the
degree-`p` étale cohomology of the colimit abelian sheaf is an isomorphism. -/
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
