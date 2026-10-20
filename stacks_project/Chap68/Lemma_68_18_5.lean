/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.PairFiber.Finite
import StacksCheckRecall

/-!
# Finite pair-fibres over monomorphic field points

In a cartesian square of algebraic spaces, the pair-fibre over a compatible pair
of points is finite when the common image is represented by a monomorphism from
the spectrum of a field and the second leg is quasi-finite at its selected point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Points

/- Lemma 68.18.5 (1): In the cartesian square of algebraic spaces over `S` with
legs `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`, the pair-fibre
`fibre p q x z` is finite if the common image `y` is represented by a
monomorphism `Spec(k) ⟶ Y` from a field and `g` is quasi-finite at `z`. -/
@[stacks 0AC7] #check
  (AlgebraicGeometry.AlgebraicSpace.Points.fibre_finite_of_mono_quasiFiniteAt :
    ∀ {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
      {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y},
      IsPullback q p g f → ∀ (x : Points X) (z : Points Z) (y : Points Y),
      map f x = y → map g z = y → ∀ (η : FieldValuedPoint Y),
      [Mono η.hom] → mk η = y → QuasiFiniteAt g z → (fibre p q x z).Finite)

/- Lemma 68.18.5 (2), tag 0AC7: In the cartesian square of algebraic spaces over `S` with
legs `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`, the pair-fibre
`fibre p q x z` is finite if `Y` is decent and `g` is étale. -/
@[stacks 0AC7] #check
  (AlgebraicGeometry.AlgebraicSpace.Points.fibre_finite_of_isDecent_etale :
    ∀ {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
      {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y},
      IsPullback q p g f → ∀ (x : Points X) (z : Points Z),
      map f x = map g z → [IsDecent Y] → [Etale g] → (fibre p q x z).Finite)

end AlgebraicGeometry.AlgebraicSpace.Points
