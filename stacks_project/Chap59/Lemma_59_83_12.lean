module

public import stacks_project.Chap59.Lemma_59_83_4_Statements
public import stacks_project.Chap59.Theorem_59_82_7_Gabber_Restrict
public import stacks_project.Chap59.Lemma_59_80_9_Pullback
public import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Etale
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Etale.TorsionOnCurve

variable {k : Type u} [Field k] [IsSepClosed k]
variable (X : SchemeOverField k) [Scheme.Hom.FiniteType X.hom] [IsSeparated X.hom]
variable [Fact (topologicalKrullDim X.left ≤ 1)]
variable (F : Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})
variable [HasSheafify X.left.smallEtaleTopology AddCommGrpCat.{u}]
variable [Abelian (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasInjectiveResolutions (Sheaf X.left.smallEtaleTopology AddCommGrpCat.{u})]
variable [HasTerminal X.left.Etale]
variable [(siteAbelianSectionsFunctor X.left.smallEtaleTopology (terminal X.left.Etale)).Additive]

/-- Lemma 59.83.12: for an extension `k'/k` of separably closed fields, `X` proper over `k` of
topological Krull dimension `≤ 1`, and a locally torsion abelian sheaf `F` on `Xₑₜ`, the
comparison `etaleCohomologyRestrict π F q` along the projection of a cartesian structure square
`X' = X ×_k k'` is an isomorphism in every degree. This is the map
`H^q_étale(X, F) ⟶ H^q_étale(X_{k'}, F|_{X_{k'}})`. -/
@[stacks 0A5E]
public theorem etaleCohomologyRestrict_isIso_of_isProper_of_isSepClosed
    (hF : IsLocallyTorsion F) (h_proper : IsProper X.hom)
    {k' : Type u} [Field k'] [IsSepClosed k'] [Algebra k k']
    (X' : SchemeOverField k') (π : X'.left ⟶ X.left)
    (h_baseChange : IsPullback π X'.hom X.hom (specMapOfAlgebra k'))
    [Scheme.Hom.FiniteType X'.hom] [IsSeparated X'.hom]
    [Abelian (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf X'.left.smallEtaleTopology AddCommGrpCat.{u})]
    [HasTerminal X'.left.Etale]
    [(siteAbelianSectionsFunctor X'.left.smallEtaleTopology (terminal X'.left.Etale)).Additive]
    [(etaleAbelianRestriction π).Additive]
    [(etaleAbelianRestriction π).PreservesHomology]
    [(etaleAbelianRestriction π).PreservesInjectiveObjects]
    [(etaleAbelianRestriction π ⋙
      siteAbelianSectionsFunctor X'.left.smallEtaleTopology (terminal X'.left.Etale)).Additive]
    (q : ℕ) :
    IsIso (etaleCohomologyRestrict π F q) := sorry

end AlgebraicGeometry.Etale.TorsionOnCurve
