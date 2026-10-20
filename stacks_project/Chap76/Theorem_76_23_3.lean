/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap76.Definition_76_23_2_FlatOnFiber

/-!
# Criterion of flatness by fibres on algebraic spaces

For a finitely presented module on an algebraic space, relative flatness over `Z` together
with fibrewise relative flatness over `Y` is equivalent, at points of the support, to
flatness of `Y` over `Z` together with relative flatness over `Y`. The common locus is open
in the support.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus of points of `|X|` at which both equivalent fibre-criterion packages hold. -/
def flatnessByFibersLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) (h : Y ⟶ Z) : Set (Points X) :=
  {x | (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt F f h x) ∧
      (FlatAt h (Points.map f x) ∧ flatOverAt F f x)}

/-- Membership in `flatnessByFibersLocus F f h` is the conjunction of the two equivalent
fibre-criterion packages. -/
theorem mem_flatnessByFibersLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (h : Y ⟶ Z) (x : Points X) :
    x ∈ flatnessByFibersLocus F f h ↔
      (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt F f h x) ∧
        (FlatAt h (Points.map f x) ∧ flatOverAt F f x) :=
  sorry

/-- Theorem 76.23.3 (1): Let `S` be a scheme. Let `f : X ⟶ Y` and `Y ⟶ Z` be morphisms of
algebraic spaces over `S`. Let `F` be a quasi-coherent `𝒪_X`-module. Assume `X` is locally
of finite presentation over `Z`, `F` is of finite presentation, and `Y` is locally of finite
type over `Z`. Let `x ∈ |X|` with images `y = Points.map f x` and `z = Points.map (f ≫ h) x`.
If `x ∈ moduleSupport F` (equivalently `¬ IsZero (stalkModuleCat xbar F)` whenever
`xbar.image = x`), then `F` is flat over `Z` at `x` and the restriction of `F` to its fibre
over `z` is flat at `x` over the fibre of `Y` over `z` if and only if `Y` is flat over `Z`
at `y` and `F` is flat over `Y` at `x`. -/
@[stacks 05X0]
theorem flatOverAt_and_fiber_iff_of_finitePresentation {S : Scheme.{u}}
    {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (h : Y ⟶ Z)
    [LocallyOfFinitePresentation (f ≫ h)] [LocallyOfFiniteType h]
    (F : X.Modules) [F.IsFinitePresentation] (x : Points X)
    (h_stalk : x ∈ moduleSupport F) :
    (flatOverAt F (f ≫ h) x ∧ flatOnFiberAt F f h x) ↔
      (FlatAt h (Points.map f x) ∧ flatOverAt F f x) :=
  sorry

/-- Theorem 76.23.3 (2): Under the same hypotheses, the set of points where both equivalent
conditions of Theorem 76.23.3 (1) hold is open in `moduleSupport F`. -/
@[stacks 05X0]
theorem isOpen_flatnessByFibersLocus {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (h : Y ⟶ Z) [LocallyOfFinitePresentation (f ≫ h)]
    [LocallyOfFiniteType h] (F : X.Modules) [F.IsFinitePresentation] :
    IsOpen ((Subtype.val : moduleSupport F → Points X) ⁻¹'
      flatnessByFibersLocus F f h) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
