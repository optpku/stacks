/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap68.«68_18_0_2_Fibre»

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

/-- Lemma 68.18.5 (1): In the cartesian square of algebraic spaces over `S` with
legs `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`, the pair-fibre
`fibre p q x z` is finite if the common image `y` is represented by a
monomorphism `Spec(k) ⟶ Y` from a field and `g` is quasi-finite at `z`. -/
@[stacks 0AC7]
theorem fibre_finite_of_mono_quasiFiniteAt
    {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback q p g f) (x : Points X) (z : Points Z) (y : Points Y)
    (hx : map f x = y) (hz : map g z = y) (η : FieldValuedPoint Y)
    [Mono η.hom] (hη : mk η = y) (hg : QuasiFiniteAt g z) :
    (fibre p q x z).Finite :=
  sorry

/-- The pair-fibre is finite if the common image `y` can be represented by a
monomorphism from the spectrum of a field and `g` is quasi-finite at `z`. -/
theorem fibre_finite_of_exists_mono_quasiFiniteAt
    {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback q p g f) (x : Points X) (z : Points Z) (y : Points Y)
    (hx : map f x = y) (hz : map g z = y)
    (hη : ∃ η : FieldValuedPoint Y, Mono η.hom ∧ mk η = y)
    (hg : QuasiFiniteAt g z) :
    (fibre p q x z).Finite :=
  sorry

/-- Lemma 68.18.5 (2): In the cartesian square of algebraic spaces over `S` with
legs `p : W ⟶ X`, `q : W ⟶ Z`, `f : X ⟶ Y`, and `g : Z ⟶ Y`, the pair-fibre
`fibre p q x z` is finite if `Y` is decent and `g` is étale. -/
@[stacks 0AC7]
theorem fibre_finite_of_isDecent_etale
    {S : Scheme.{u}} {W X Y Z : AlgebraicSpace S}
    {p : W ⟶ X} {q : W ⟶ Z} {f : X ⟶ Y} {g : Z ⟶ Y}
    (h : IsPullback q p g f) (x : Points X) (z : Points Z)
    (hy : map f x = map g z) [IsDecent Y] [Etale g] :
    (fibre p q x z).Finite :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Points
