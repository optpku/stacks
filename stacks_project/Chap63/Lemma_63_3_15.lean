module

public import stacks_project.Chap63.Lemma_63_3_15_Directed

/-!
# Directed open coverings of the source: colimits of `f_!`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y) (U : ι → X.Opens)
variable [IsSeparated f] [LocallyOfFiniteType f]

/-- Lemma 63.3.15: if `f : X ⟶ Y` is separated and locally of finite type and
`U : ι → X.Opens` is a Zariski open covering directed under inclusion
(`Directed (· ≤ ·) U`, i.e. for all `i, j` there exists `k` with
`U i ⊔ U j ≤ U k`), then `f_! F` is the colimit of `f_{i,!}(F|_{U i})` in
`Ab(Y_étale)`, functorially in `F`, with transition maps the covariance maps
of Remark 63.3.5. -/
@[stacks 0F54]
instance etaleLowerShriekDirectedComparison_isIso
    [Fact (IsOpenCover U)] [Fact (Directed (· ≤ ·) U)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)] :
    IsIso (etaleLowerShriekDirectedComparisonApp f U F) :=
  sorry

/-- The identification `colim_i f_{i,!}(F|_{U i}) ≅ f_! F` along a directed
Zariski open covering of the source. -/
abbrev etaleLowerShriekDirectedIso
    [Fact (IsOpenCover U)] [Fact (Directed (· ≤ ·) U)]
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)] :
    colimit (etaleLowerShriekDirectedDiagram f U F) ≅ (etaleLowerShriek f).obj F :=
  asIso (etaleLowerShriekDirectedComparisonApp f U F)

/-- Explicit covering hypotheses yield that the canonical comparison
`colim_i f_{i,!}(F|_{U i}) ⟶ f_! F` is an isomorphism. -/
theorem etaleLowerShriekDirectedComparison_isIso_of_openCover
    (hcover : IsOpenCover U) (hdir : Directed (· ≤ ·) U)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
    [HasColimit (etaleLowerShriekDirectedDiagram f U F)] :
    IsIso (etaleLowerShriekDirectedComparisonApp f U F) :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
