/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.WeilCohomology.MotivicRealization.ClassicalAxioms

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

/- Proposition 45.7.11: a classical Weil cohomology theory over an algebraically
closed field `k` with coefficients in a characteristic-zero field `F` is a ℚ-linear
strong monoidal functor `G` from Chow motives to graded `F`-vector spaces together
with `F[2] ≅ G(𝟙(1))`, such that `G(h(X))` vanishes in negative degrees and
`Module.finrank F` of degree zero equals `1` for every smooth projective variety `X`.
Given a `ClassicalCore`, range vanishing and a bijective top-degree trace are
equivalent to those two extra conditions. -/
@[stacks 0FH3]
#check (WeilCohomology.MotivicRealization.ClassicalCore.fullAxioms_iff :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      {F : Type v} [Field F] [CharZero F]
      {G : ChowMotive k (fun _ ↦ Correspondence.GradedCategory k) ⥤
        GradedObject ℤ (ModuleCat F)}
      [G.Linear ℚ] [G.Monoidal] (C : WeilCohomology.MotivicRealization.ClassicalCore G),
      ((∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom]
          [EquidimensionalSpace X.left] (d : ℕ),
          topologicalKrullDim X.left = (d : WithBot ℕ∞) →
            ∀ i : ℤ, i < 0 ∨ 2 * (d : ℤ) < i →
              IsZero ((G.obj (ChowMotive.h X)) i)) ∧
        ∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom]
          [EquidimensionalSpace X.left] (d : ℕ)
          (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞)),
          Function.Bijective (C.integral X d hXdim).hom) ↔
      ((∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom]
          (i : ℤ), i < 0 → IsZero ((G.obj (ChowMotive.h X)) i)) ∧
        ∀ (X : SchemeOverField k) [Variety X] [Smooth X.hom] [Projective X.hom],
          Module.finrank F ((G.obj (ChowMotive.h X)) 0) = 1))
