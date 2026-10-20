/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Contraction.Existence
import StacksCheckRecall

/-!
# Artin's theorem on contractions under quasi-separated hypotheses

Over a locally Noetherian scheme whose stalks at finite type points are
G-rings, a contraction situation with `X'` and `W` quasi-separated over the
base admits a solution.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.SchemeRealization
open AlgebraicGeometry.AlgebraicSpace.ContractionSituation

universe u

/- Remark 98.27.18: Artin's contraction theorem still holds after replacing
the hypotheses that `X'` and `W` are separated over `S` by the hypotheses
that they are quasi-separated over `S`. Representability of the diagonal of
the contraction functor can be bootstrapped from the always-separated
equalizer triples of Remark 98.27.7; the remaining use of separatedness is
to produce a morphism `x' : V' ⟶ X'`, which exists already if `X' ⟶ S` is
quasi-separated by Remark 76.43.4. Thus if `S` is locally Noetherian with
G-ring stalks at finite type points, a contraction situation `σ` with `X'`
and `W` quasi-separated over `S` admits an algebraic space `X` locally of
finite type over `S` together with a `SolutionFor σ X`. -/
@[stacks 0GIC] #check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.exists_solutionFor_of_quasiSeparated :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S)
      [QuasiSeparated (toBase σ.X')] [FormalAlgebraicSpace.QuasiSeparated (toBaseW σ)]
      (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)),
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X)),
      Nonempty (SolutionFor σ X))

/- Unpacking of `exists_solutionFor_of_quasiSeparated`: there is an algebraic
space `X` locally of finite type over `S` and a solution `sol : SolutionFor σ X`
with `Proper sol.f`, `IsIso sol.a`, inverse image of `sol.T` equal to `σ.T'`,
isomorphism over the open complement of `sol.T`, and
`sol.mapCompletion ≫ sol.a = σ.g`. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.ContractionSituation.exists_solutionFor_of_quasiSeparated_spec :
    ∀ {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
      (σ : ContractionSituation S)
      [QuasiSeparated (toBase σ.X')] [FormalAlgebraicSpace.QuasiSeparated (toBaseW σ)]
      (hG : ∀ s : S, IsFiniteTypePoint s → IsGRing (S.presheaf.stalk s)),
    ∃ (X : AlgebraicSpace S) (_ : LocallyOfFiniteType (toBase X))
      (sol : SolutionFor σ X),
      Proper sol.f ∧ IsIso sol.a ∧
        σ.T' = sol.T.preimage (Points.continuous_map sol.f) ∧
        IsIsoOverOpen sol.f (AlgebraicSpace.openComplementι X sol.T) ∧
        sol.mapCompletion ≫ sol.a = σ.g)
