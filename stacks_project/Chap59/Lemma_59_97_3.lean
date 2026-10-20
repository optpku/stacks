module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.ClosedPointSupport
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Sheaf
open AlgebraicGeometry

noncomputable section

universe u

/- Lemma 59.97.3 (1): if `K` is a separably closed field, `X` is a scheme of finite
type over `K`, and `F` is an abelian sheaf on `X.left.smallEtaleTopology` with
`abelianSheafSupport F ⊆ closedPoints X.left`, then
`IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj F)` for every `q > 0`. -/
@[stacks 0F1F] #check
  (AlgebraicGeometry.Scheme.Etale.etaleCohomology_isZero_of_support_closedPoints :
    ∀ {K : Type u} [Field K] [IsSepClosed K] (X : SchemeOverField K) [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    AlgebraicGeometry.Scheme.Etale.abelianSheafSupport F ⊆ closedPoints X.left →
    ∀ (q : ℕ), 0 < q →
    IsZero ((Sheaf.functorH X.left.smallEtaleTopology q).obj F))

/- Lemma 59.97.3 (2): if `K` is a separably closed field, `X` is a scheme of finite
type over `K`, and `F` is an abelian sheaf on `X.left.smallEtaleTopology` with
`abelianSheafSupport F ⊆ closedPoints X.left`, then `F` is globally generated. -/
@[stacks 0F1F] #check
  (AlgebraicGeometry.Scheme.Etale.isGloballyGenerated_of_support_closedPoints :
    ∀ {K : Type u} [Field K] [IsSepClosed K] (X : SchemeOverField K) [Algebraic X]
    [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
    [HasTerminal X.left.Etale]
    (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u}),
    AlgebraicGeometry.Scheme.Etale.abelianSheafSupport F ⊆ closedPoints X.left →
    AlgebraicGeometry.Scheme.Etale.IsGloballyGenerated F)

end
