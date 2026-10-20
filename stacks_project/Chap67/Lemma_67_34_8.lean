/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Dimension

/-!
# Quasi-finiteness at a point of a field fibre of an algebraic space

A locally finite-type morphism of algebraic spaces is quasi-finite at the
image of a zero-dimensional point of a field fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 67.34.8: Let `S` be a scheme. Consider a cartesian square
`IsPullback p q f g.hom` of algebraic spaces over `S`, with `p : F ⟶ X`,
`f : X ⟶ Y` locally of finite type, and `g : FieldValuedPoint Y` giving
the morphism `Spec(k) ⟶ Y` from the spectrum of a field over `S`. If
`z : Points F` satisfies `dimensionAt z = 0`, then after replacing `X` by
an open subspace containing `Points.map p z` the morphism `X ⟶ Y` is
locally quasi-finite, i.e. `QuasiFiniteAt f (Points.map p z)`. -/
@[stacks 06LS] #check
  (AlgebraicGeometry.AlgebraicSpace.quasiFiniteAt_of_dimensionAt_eq_zero :
    ∀ {S : Scheme.{u}} {X Y F : AlgebraicSpace S}
      (f : X ⟶ Y) [LocallyOfFiniteType f]
      (g : FieldValuedPoint Y) (p : F ⟶ X) (q : F ⟶ ofOver g.overObj)
      (hpb : IsPullback p q f g.hom) (z : Points F)
      (hz : dimensionAt z = (0 : WithBot ℕ∞)),
      QuasiFiniteAt f (Points.map p z))

end AlgebraicGeometry.AlgebraicSpace
