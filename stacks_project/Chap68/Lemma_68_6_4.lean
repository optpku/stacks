module

public import stacks_project.Chap68.Lemma_68_6_4_Approximation
public import stacks_project.Chap68.Lemma_68_17_4_Relative

/-!
# Reasonable quasi-compact algebraic spaces as filtered sheaf colimits

A quasi-compact reasonable algebraic space is a filtered colimit, in the fppf sheaf
category, of quasi-compact quasi-separated algebraic spaces with étale surjective
transitions and coprojections.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.6.4: Let `S` be a scheme and let `X` be a quasi-compact reasonable algebraic
space over `S`. Then there exists a small filtered diagram of quasi-compact quasi-separated
algebraic spaces `Xᵢ` such that `X` is the colimit of the `Xᵢ` in the category of fppf
sheaves on `Over S`. Moreover the diagram may be arranged so that for every quasi-compact
scheme `T` over `S` one has `colim Xᵢ(T) = X(T)`, the transition morphisms and the
coprojections `Xᵢ ⟶ X` are surjective and étale, and if `X` is a scheme then the `Xᵢ` are
schemes and the transition morphisms and coprojections are local isomorphisms. -/
@[stacks 03K0]
theorem exists_qcqs_etale_approximation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsReasonable X] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X),
      IsQCQSEtaleApproximation F ι ∧
        (IsScheme X → IsQCQSLocalIsoApproximation F ι) :=
  sorry

/-- A quasi-compact reasonable scheme, viewed as an algebraic space, admits a filtered
qcqs étale approximation whose objects are schemes and whose transitions and coprojections
are local isomorphisms. -/
theorem exists_qcqs_localIso_approximation {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsReasonable X] [IsScheme X] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (F : J ⥤ AlgebraicSpace S) (ι : F ⟶ (Functor.const J).obj X),
      IsQCQSEtaleApproximation F ι ∧ IsQCQSLocalIsoApproximation F ι :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
