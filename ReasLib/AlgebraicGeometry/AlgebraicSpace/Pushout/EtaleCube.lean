/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

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
face is a scheme pushout along a thickening and an affine morphism and remains a pushout
after applying `ofOverMap`. The remaining four faces are cartesian, and the northeast arrows
are surjective étale. -/
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

  /-- The front face is a pushout in the category of schemes over `S`. -/
  isPushout_front_scheme : IsPushout i1 f1 i1' g1
  /-- The front horizontal morphism is a thickening of schemes. -/
  isThickening_i1 : AlgebraicGeometry.IsThickening i1.left
  /-- The front left vertical morphism is affine. -/
  isAffineHom_f1 : IsAffineHom f1.left

namespace Cube

/-- Assemble a pushout-along-thickening cube from vertices, arrows, and proofs of all
its geometric laws. -/
def of {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
    {Y1 : Over S} {πY : ofOver Y1 ⟶ Y}
    (X1 X1' Y1' : Over S)
    (i1 : X1 ⟶ X1') (f1 : X1 ⟶ Y1) (i1' : X1' ⟶ Y1') (g1 : Y1 ⟶ Y1')
    (πX : ofOver X1 ⟶ X) (πX' : ofOver X1' ⟶ X') (πY' : ofOver Y1' ⟶ Y')
    (isPushout_back : IsPushout i f i' g)
    (isPushout_front : IsPushout (ofOverMap i1) (ofOverMap f1) (ofOverMap i1') (ofOverMap g1))
    (isPullback_top : IsPullback (ofOverMap i1) πX πX' i)
    (isPullback_left : IsPullback (ofOverMap f1) πX πY f)
    (isPullback_right : IsPullback (ofOverMap i1') πX' πY' i')
    (isPullback_bottom : IsPullback (ofOverMap g1) πY πY' g)
    (etale_πX : Etale πX)
    (surjective_πX : Surjective πX)
    (etale_πX' : Etale πX')
    (surjective_πX' : Surjective πX')
    (etale_πY : Etale πY)
    (surjective_πY : Surjective πY)
    (etale_πY' : Etale πY')
    (surjective_πY' : Surjective πY')
    (isPushout_front_scheme : IsPushout i1 f1 i1' g1)
    (isThickening_i1 : AlgebraicGeometry.IsThickening i1.left)
    (isAffineHom_f1 : IsAffineHom f1.left) :
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
  isPushout_back := isPushout_back
  isPushout_front := isPushout_front
  isPullback_top := isPullback_top
  isPullback_left := isPullback_left
  isPullback_right := isPullback_right
  isPullback_bottom := isPullback_bottom
  etale_πX := etale_πX
  surjective_πX := surjective_πX
  etale_πX' := etale_πX'
  surjective_πX' := surjective_πX'
  etale_πY := etale_πY
  surjective_πY := surjective_πY
  etale_πY' := etale_πY'
  surjective_πY' := surjective_πY'
  isPushout_front_scheme := isPushout_front_scheme
  isThickening_i1 := isThickening_i1
  isAffineHom_f1 := isAffineHom_f1

variable {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
variable {i : X ⟶ X'} {f : X ⟶ Y} {i' : X' ⟶ Y'} {g : Y ⟶ Y'}
variable {Y1 : Over S} {πY : ofOver Y1 ⟶ Y}

/-- A pushout-along-thickening cube has pushout front and back faces, cartesian remaining
faces, and surjective étale northeast arrows; its scheme front face is a pushout along
a thickening and an affine morphism. -/
theorem spec (C : Cube i f i' g πY) :
    (IsPushout i f i' g ∧
      IsPushout (ofOverMap C.i1) (ofOverMap C.f1) (ofOverMap C.i1') (ofOverMap C.g1)) ∧
    (IsPullback (ofOverMap C.i1) C.πX C.πX' i ∧
      IsPullback (ofOverMap C.f1) C.πX πY f ∧
      IsPullback (ofOverMap C.i1') C.πX' C.πY' i' ∧
      IsPullback (ofOverMap C.g1) πY C.πY' g) ∧
    ((Etale C.πX ∧ Surjective C.πX) ∧ (Etale C.πX' ∧ Surjective C.πX') ∧
      (Etale πY ∧ Surjective πY) ∧ (Etale C.πY' ∧ Surjective C.πY')) ∧
    (IsPushout C.i1 C.f1 C.i1' C.g1 ∧
      AlgebraicGeometry.IsThickening C.i1.left ∧ IsAffineHom C.f1.left) :=
  ⟨⟨C.isPushout_back, C.isPushout_front⟩,
    ⟨C.isPullback_top, C.isPullback_left, C.isPullback_right, C.isPullback_bottom⟩,
    ⟨⟨C.etale_πX, C.surjective_πX⟩, ⟨C.etale_πX', C.surjective_πX'⟩,
      ⟨C.etale_πY, C.surjective_πY⟩, ⟨C.etale_πY', C.surjective_πY'⟩⟩,
    ⟨C.isPushout_front_scheme, C.isThickening_i1, C.isAffineHom_f1⟩⟩

end Cube

/-- A pushout of algebraic spaces along a thickening and an affine morphism admits a
scheme presentation cube over any prescribed surjective étale scheme atlas of its lower
left vertex. The front scheme square is a pushout along a thickening and an affine morphism,
the back square is the given pushout, the four side faces are cartesian, and the northeast
arrows are surjective étale. -/
theorem exists_cube {S : Scheme.{u}} {X X' Y Y' : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) (i' : X' ⟶ Y') (g : Y ⟶ Y')
    [IsThickening i] [Affine f] (h : IsPushout i f i' g)
    {Y1 : Over S} (πY : ofOver Y1 ⟶ Y) [Etale πY] [Surjective πY] :
    Nonempty (Cube i f i' g πY) :=
  sorry

/-- A pushout of the overlap maps of a triple over a thickening and an affine morphism
admits a scheme presentation cube over any prescribed surjective étale scheme atlas of
the triple's lower left vertex. The upper left scheme vertex is the fibre product of that
atlas with the domain of the original affine morphism, with the indicated projections. -/
theorem exists_cube_over {S : Scheme.{u}} {X X' Y V U' G : AlgebraicSpace S}
    (i : X ⟶ X') (f : X ⟶ Y) [IsThickening i] [Affine f]
    (pV : V ⟶ Y) (pU' : U' ⟶ X')
    (φ : Limits.pullback pV f ≅ Limits.pullback pU' i)
    (hφ : φ.hom ≫ Limits.pullback.snd pU' i = Limits.pullback.snd pV f)
    (inlG : V ⟶ G) (inrG : U' ⟶ G)
    (hG : IsPushout (Limits.pullback.fst pU' i)
      (φ.inv ≫ Limits.pullback.fst pV f) inrG inlG)
    {V1 : Over S} (πV : ofOver V1 ⟶ V) [Etale πV] [Surjective πV] :
    ∃ C : Cube (Limits.pullback.fst pU' i)
        (φ.inv ≫ Limits.pullback.fst pV f) inrG inlG πV,
      IsPullback (ofOverMap C.f1) (C.πX ≫ Limits.pullback.snd pU' i) (πV ≫ pV) f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PushoutAlongThickening
