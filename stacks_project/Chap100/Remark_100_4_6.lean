module

public import stacks_project.Chap100.Remark_100_4_6_Quotient
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open scoped Bicategory

/- Remark 100.4.6 (1): let `X` be an algebraic stack. Let `U` be an algebraic
space and let `f : U ⟶ X` be a surjective morphism in the sense of
Section 100.3. Let `R = U ×_X U` and let `(U, R, s, t, c)` be the associated
groupoid in algebraic spaces. Then the image of `|R| → |U| × |U|` is an
equivalence relation on `|U|`. -/
@[stacks 04XK] #check
  (pointsRel_equivalence :
    ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
      [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
      [Groupoids.Hom.Surjective f],
      Equivalence (pointsRel f hU))

/- Remark 100.4.6 (2): in the same setup, with `fCan : [U / R] ⟶ X` the
canonical morphism of Algebraic Stacks, Lemma 94.16.1, one has
`|X| = |U| / |R|`. In general `[U / R]` need not be an algebraic stack, and
`fCan` need not be an isomorphism. -/
@[stacks 04XK] #check
  (isPointsQuotient :
    ∀ {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)
      [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U)
      [Groupoids.Hom.Surjective f],
      Function.Surjective (pointsMap f hU) ∧
        ∀ u v, pointsRel f hU u v ↔ pointsMap f hU u = pointsMap f hU v)
