module

public import stacks_project.Chap102.Lemma_102_6_2_Factorization
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

universe u

/- Lemma 102.6.2: a finite type separated morphism `f : 𝒳 ⟶ Y` from an
algebraic stack to a quasi-compact quasi-separated algebraic space factors,
over `Y`, through a closed immersion `𝒳 ⟶ 𝒳'` into an algebraic stack
`𝒳'` whose structure morphism `f' : 𝒳' ⟶ Y` is separated and of finite
presentation. -/
@[stacks 0CQ2] #check
  (exists_closedImmersion_factorization_of_finiteType_separated :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      {Y : AlgebraicSpace S} [AlgebraicSpace.IsQuasiCompact Y]
      [AlgebraicSpace.IsAbsolutelyQuasiSeparated Y]
      (f : X ⟶ Y.toGroupoids) [FiniteType f] [Separated f],
      ∃ (X' : GroupoidsOver S) (_ : AlgebraicStack X')
        (f' : X' ⟶ Y.toGroupoids) (_ : FinitePresentation f')
        (_ : Separated f')
        (i : X ⟶ X') (_ : Groupoids.Hom.ClosedImmersion i),
        Nonempty (i ≫ f' ≅ f))
