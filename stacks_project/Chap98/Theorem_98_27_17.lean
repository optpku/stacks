/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap98.Lemma_98_27_6_Solution
public import stacks_project.Chap98.Lemma_98_27_9
import Mathlib.Tactic.CrossRefAttribute

/-!
# Artin's theorem on contractions

Over a locally Noetherian scheme whose stalks at finite type points are
G-rings, a contraction situation with `X'` and `W` separated over the base
admits a solution.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ContractionSituation

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]

/-- Theorem 98.27.17: let `S` be a locally Noetherian scheme such that
`S.presheaf.stalk s` is a G-ring for every finite type point `s` of `S`.
In a contraction situation `σ`, if `X'` and `W` are separated over `S`,
then there exists an algebraic space `X` locally of finite type over `S`
together with a proper morphism `f : σ.X' ⟶ X`, a closed subset
`T ⊂ Points X`, and an isomorphism `a : completionAlong X T ⟶ σ.W` such
that `σ.T'` is the inverse image of `T` by `Points.map f`, `f` identifies
the open complements of `T'` and `T`, and `σ.g = a ∘ f_/T`. In other
words, `(f, T, a)` is a `SolutionFor σ X`. -/
@[stacks 0GIB]
theorem exists_solutionFor (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
      Nonempty (SolutionFor σ X) :=
  sorry

/-- Unpacking of `exists_solutionFor`: there is an algebraic space `X`
locally of finite type over `S` and a solution `sol : SolutionFor σ X`
with `Proper sol.f`, `IsIso sol.a`, inverse image of `sol.T` equal to
`σ.T'`, isomorphism over the open complement of `sol.T`, and
`sol.mapCompletion ≫ sol.a = σ.g`. -/
theorem exists_solutionFor_spec (σ : ContractionSituation S)
    [Separated (toBase σ.X')] [FormalAlgebraicSpace.Separated (toBaseW σ)]
    (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)) :
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X))
      (sol : SolutionFor σ X),
      Proper sol.f ∧ IsIso sol.a ∧
        σ.T' = sol.T.preimage (Points.continuous_map sol.f) ∧
        IsIsoOverOpen sol.f (AlgebraicSpace.openComplementι X sol.T) ∧
        sol.mapCompletion ≫ sol.a = σ.g :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ContractionSituation
