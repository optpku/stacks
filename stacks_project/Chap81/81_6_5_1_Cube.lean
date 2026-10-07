module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Pushout-along-thickening cubes

A commutative cube relating a pushout of algebraic spaces along a thickening and an affine
morphism to a scheme-level pushout, with cartesian side faces and surjective étale northeast
arrows.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening

/-- A commutative cube with algebraic-space vertices `X`, `X'`, `Y`, `Y'` and scheme vertices
`X1`, `X1'`, `Y1`, `Y1'` over `S`. The back face is the given space-level square, the front
face is the image under `ofOverMap` of a scheme-level square, the remaining four faces are
cartesian, and the northeast arrows are surjective étale. -/
structure Cube {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    {Y1 : Over S} (πY : ofOver Y1 ⟶ Y) where
  /-- The scheme vertex over `X`. -/
  X1 : Over S
  /-- The scheme vertex over `X'`. -/
  X1' : Over S
  /-- The scheme vertex over `Y'`. -/
  Y1' : Over S
  /-- The front thickening, as a morphism of schemes over `S`. -/
  i1 : X1 ⟶ X1'
  /-- The front affine morphism, as a morphism of schemes over `S`. -/
  f1 : X1 ⟶ Y1
  /-- The front right vertical arrow, as a morphism of schemes over `S`. -/
  i1' : X1' ⟶ Y1'
  /-- The front bottom arrow, as a morphism of schemes over `S`. -/
  g1 : Y1 ⟶ Y1'
  /-- The northeast arrow from `X1` to `X`. -/
  πX : ofOver X1 ⟶ X
  /-- The northeast arrow from `X1'` to `X'`. -/
  πX' : ofOver X1' ⟶ X'
  /-- The northeast arrow from `Y1'` to `Y'`. -/
  πY' : ofOver Y1' ⟶ Y'
  /-- The back face is a pushout of algebraic spaces. -/
  isPushout_back : IsPushout i f i' g
  /-- The front face is a pushout after viewing schemes as algebraic spaces. -/
  isPushout_front :
    IsPushout (ofOverMap i1) (ofOverMap f1) (ofOverMap i1') (ofOverMap g1)
  /-- The top face is cartesian. -/
  isPullback_top : IsPullback (ofOverMap i1) πX πX' i
  /-- The left face is cartesian. -/
  isPullback_left : IsPullback (ofOverMap f1) πX πY f
  /-- The right face is cartesian. -/
  isPullback_right : IsPullback (ofOverMap i1') πX' πY' i'
  /-- The bottom face is cartesian. -/
  isPullback_bottom : IsPullback (ofOverMap g1) πY πY' g
  /-- The northeast arrow `πX` is étale. -/
  etale_πX : Etale πX
  /-- The northeast arrow `πX` is surjective. -/
  surjective_πX : Surjective πX
  /-- The northeast arrow `πX'` is étale. -/
  etale_πX' : Etale πX'
  /-- The northeast arrow `πX'` is surjective. -/
  surjective_πX' : Surjective πX'
  /-- The northeast arrow `πY` is étale. -/
  etale_πY : Etale πY
  /-- The northeast arrow `πY` is surjective. -/
  surjective_πY : Surjective πY
  /-- The northeast arrow `πY'` is étale. -/
  etale_πY' : Etale πY'
  /-- The northeast arrow `πY'` is surjective. -/
  surjective_πY' : Surjective πY'

namespace Cube

/-- Pack given vertices and arrows into a pushout-along-thickening cube. -/
def of {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    {Y1 : Over S} {πY : ofOver Y1 ⟶ Y}
    (X1 X1' Y1' : Over S)
    (i1 : X1 ⟶ X1') (f1 : X1 ⟶ Y1) (i1' : X1' ⟶ Y1') (g1 : Y1 ⟶ Y1')
    (πX : ofOver X1 ⟶ X) (πX' : ofOver X1' ⟶ X') (πY' : ofOver Y1' ⟶ Y') :
    Cube i f i' g πY where
  X1 := X1
  X1' := X1'
  Y1' := Y1'
  i1 := i1
  f1 := f1
  i1' := i1'
  g1 := g1
  πX := πX
  πX' := πX'
  πY' := πY'
  isPushout_back := sorry
  isPushout_front := sorry
  isPullback_top := sorry
  isPullback_left := sorry
  isPullback_right := sorry
  isPullback_bottom := sorry
  etale_πX := sorry
  surjective_πX := sorry
  etale_πX' := sorry
  surjective_πX' := sorry
  etale_πY := sorry
  surjective_πY := sorry
  etale_πY' := sorry
  surjective_πY' := sorry

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
variable {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
variable {Y1 : Over S} {πY : ofOver Y1 ⟶ Y}

/-- A pushout-along-thickening cube has pushout front and back faces, cartesian remaining
faces, and surjective étale northeast arrows. -/
theorem spec (C : Cube i f i' g πY) :
    (IsPushout i f i' g ∧
      IsPushout (ofOverMap C.i1) (ofOverMap C.f1) (ofOverMap C.i1') (ofOverMap C.g1)) ∧
    (IsPullback (ofOverMap C.i1) C.πX C.πX' i ∧
      IsPullback (ofOverMap C.f1) C.πX πY f ∧
      IsPullback (ofOverMap C.i1') C.πX' C.πY' i' ∧
      IsPullback (ofOverMap C.g1) πY C.πY' g) ∧
    ((Etale C.πX ∧ Surjective C.πX) ∧ (Etale C.πX' ∧ Surjective C.πX') ∧
      (Etale πY ∧ Surjective πY) ∧ (Etale C.πY' ∧ Surjective C.πY')) :=
  sorry

end Cube

end AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening
