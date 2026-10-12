/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Correspondence.GraphAction

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

/- Lemma 45.3.6 (1) -/
@[stacks 0FG5] #check (AlgebraicGeometry.Correspondence.pushforward_graph :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Smooth X.hom]
    [Projective X.hom] [Smooth Y.hom] [Projective Y.hom] (f : Y ⟶ X) (s : ℤ)
    (alpha : RationalChowCohomology X s),
    castCohomologyDegree (Int.add_zero s)
      (pushforward X Y 0 s (rationalGraph f) alpha) = cohomologyPullback f s alpha)

/- Lemma 45.3.6 (2) -/
@[stacks 0FG5] #check (AlgebraicGeometry.Correspondence.pullback_graph :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Smooth X.hom]
    [Projective X.hom] [Smooth Y.hom] [Projective Y.hom] (f : Y ⟶ X) (s : ℤ)
    (alpha : RationalChowHomology Y (-s)),
    castHomologyDegree (congrArg Neg.neg (Int.zero_add s))
      (pullback X Y 0 s (rationalGraph f) alpha) = homologyPushforward f (-s) alpha)

/- Lemma 45.3.6 (3) -/
@[stacks 0FG5] #check (AlgebraicGeometry.Correspondence.pushforward_transposedGraph :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Smooth X.hom]
    [Projective X.hom] [EquidimensionalSpace X.left] [Smooth Y.hom]
    [Projective Y.hom] [EquidimensionalSpace Y.left] (d e : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) (s : ℤ)
    (alpha : RationalChowCohomology Y s),
    castHomologyDegree (transposedPushforwardDegree d e s)
      (poincareDuality X d (s + ((d : ℤ) - (e : ℤ) + 0))
        (pushforward Y X ((d : ℤ) - (e : ℤ) + 0) s
          (transposedGraph X Y d e hXdim hYdim f) alpha)) =
      homologyPushforward f ((e : ℤ) - s) (poincareDuality Y e s alpha))

/- Lemma 45.3.6 (4) -/
@[stacks 0FG5] #check (AlgebraicGeometry.Correspondence.pullback_transposedGraph :
  ∀ {k : Type u} [Field k] {X Y : SchemeOverField k} [Smooth X.hom]
    [Projective X.hom] [EquidimensionalSpace X.left] [Smooth Y.hom]
    [Projective Y.hom] [EquidimensionalSpace Y.left] (d e : ℕ)
    (hXdim : topologicalKrullDim X.left = (d : WithBot ℕ∞))
    (hYdim : topologicalKrullDim Y.left = (e : WithBot ℕ∞)) (f : Y ⟶ X) (s : ℤ)
    (alpha : RationalChowCohomology X s),
    castHomologyDegree (transposedPullbackOutputDegree d e s)
      (pullback Y X ((d : ℤ) - (e : ℤ) + 0) (s - (d : ℤ))
        (transposedGraph X Y d e hXdim hYdim f)
        (castHomologyDegree (transposedPullbackInputDegree d s)
          (poincareDuality X d s alpha))) =
      poincareDuality Y e s (cohomologyPullback f s alpha))

end AlgebraicGeometry.Correspondence
