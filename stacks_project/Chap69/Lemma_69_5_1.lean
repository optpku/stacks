module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Cohomology
import StacksCheckRecall

/-!
# Lemma 69.5.1

Filtered colimits of abelian étale sheaves commute with cohomology on a
quasi-compact quasi-separated algebraic space.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

/- Lemma 69.5.1: Let `S` be a scheme. Let `X` be an algebraic space over `S`.
If `X` is quasi-compact and quasi-separated, then for every filtered diagram
`ℱ` of abelian sheaves on `X_étale` and every `p : ℕ`, the canonical map
`colimit.post ℱ (Sheaf.functorH (smallEtaleTopology X) p)` is an isomorphism. -/
@[stacks 073E] #check
  (AlgebraicGeometry.AlgebraicSpace.functorH_colimitComparison_isIso :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    [HasSheafify (smallEtaleTopology X) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    {I : Type (u + 1)} [Category.{u + 1} I] [IsFiltered I]
    (ℱ : I ⥤ Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})
    [HasColimit ℱ] (p : ℕ)
    [HasColimit (ℱ ⋙ Sheaf.functorH (smallEtaleTopology X) p)],
    IsIso (colimit.post ℱ (Sheaf.functorH (smallEtaleTopology X) p)))
