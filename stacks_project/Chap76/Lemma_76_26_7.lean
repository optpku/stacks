/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_26_7_CohenMacaulay

/-!
# Openness of the Cohen--Macaulay locus of a morphism of algebraic spaces

If `f : X ⟶ Y` is a flat, locally of finite presentation morphism of
algebraic spaces over a scheme `S`, then the locus of points of `X` at which
`f` is Cohen--Macaulay is open, and it commutes with arbitrary base change of
`f`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.26.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is flat and locally of finite presentation.
Then `cohenMacaulayLocus f` is open in `Points X`. -/
@[stacks 0E10]
theorem isOpen_cohenMacaulayLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] [LocallyOfFinitePresentation f] :
    IsOpen (cohenMacaulayLocus f) :=
  sorry

/-- Lemma 76.26.7 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S` which is flat and locally of finite presentation.
For a cartesian square with `g' : X' ⟶ X`, `f' : X' ⟶ Y'`, `f : X ⟶ Y`, and
`g : Y' ⟶ Y`, the Cohen--Macaulay locus of `f'` equals the inverse image of
`cohenMacaulayLocus f` under `Points.map g'`. -/
@[stacks 0E10]
theorem cohenMacaulayLocus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f] :
    cohenMacaulayLocus f' = Points.map g' ⁻¹' cohenMacaulayLocus f :=
  sorry

/-- A point of `Points X'` lies in the Cohen--Macaulay locus of `f'` if and only
if its image under `Points.map g'` lies in `cohenMacaulayLocus f`. -/
theorem mem_cohenMacaulayLocus_eq_preimage_of_isPullback {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat f]
    [LocallyOfFinitePresentation f] (x' : Points X') :
    x' ∈ cohenMacaulayLocus f' ↔
      Points.map g' x' ∈ cohenMacaulayLocus f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
