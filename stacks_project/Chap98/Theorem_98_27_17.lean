module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Existence
import StacksCheckRecall

/-!
# Artin's theorem on contractions

Over a locally Noetherian scheme whose stalks at finite type points are
G-rings, a contraction situation with `X'` and `W` separated over the base
admits a solution.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open AlgebraicGeometry.AlgebraicSpace.ContractionSituation

universe u

/- Theorem 98.27.17: let `S` be a locally Noetherian scheme such that
`S.presheaf.stalk s` is a G-ring for every finite type point `s` of `S`.
In a contraction situation `σ`, if `X'` and `W` are separated over `S`,
then there exists an algebraic space `X` locally of finite type over `S`
together with a proper morphism `f : σ.X' ⟶ X`, a closed subset
`T ⊂ Points X`, and an isomorphism `a : completionAlong X T ⟶ σ.W` such
that `σ.T'` is the inverse image of `T` by `Points.map f`, `f` identifies
the open complements of `T'` and `T`, and `σ.g = a ∘ f_/T`. In other
words, `(f, T, a)` is a `SolutionFor σ X`. -/
@[stacks 0GIB] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.exists_solutionFor :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S)
      [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)]
      (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)),
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
      Nonempty (SolutionFor σ X))
