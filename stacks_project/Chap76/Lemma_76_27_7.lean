/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Locus
import StacksCheckRecall

/-!
# Openness of the Gorenstein locus of a morphism of algebraic spaces

If `f : X ⟶ Y` is a flat, locally of finite presentation morphism of
algebraic spaces over a scheme `S`, then the locus of points of `X` at which
`f` is Gorenstein is open, and it commutes with arbitrary base change of `f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

/- Lemma 76.27.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is flat and locally of finite presentation.
Then the Gorenstein locus `W = gorensteinLocus f` is open in `Points X`. -/
@[stacks 0E19] #check
  (AlgebraicGeometry.AlgebraicSpace.isOpen_gorensteinLocus :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
      (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f],
      IsOpen (gorensteinLocus f))

/- Lemma 76.27.7 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is flat and locally of finite presentation.
For any morphism `g : Y' ⟶ Y`, writing `f' = pullback.snd f g` and
`g' = pullback.fst f g`, the Gorenstein locus `W'` of `f'` equals
`W' = g' ⁻¹' W`. -/
@[stacks 0E19] #check
  (AlgebraicGeometry.AlgebraicSpace.gorensteinLocus_pullback_snd :
    ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
      (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (g : Y' ⟶ Y),
      gorensteinLocus (pullback.snd f g) =
        Points.map (pullback.fst f g) ⁻¹' gorensteinLocus f)

/- Pointwise form of base change for the Gorenstein locus: `f'` is Gorenstein
at `x'` if and only if `f` is Gorenstein at `g' x'`. -/
#check (AlgebraicGeometry.AlgebraicSpace.gorensteinAt_iff_of_pullback_snd :
  ∀ {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] (g : Y' ⟶ Y)
    (x' : Points (pullback f g)),
    GorensteinAt (pullback.snd f g) x' ↔
      GorensteinAt f (Points.map (pullback.fst f g) x'))
