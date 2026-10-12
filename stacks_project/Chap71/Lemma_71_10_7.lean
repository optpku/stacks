/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap71.Lemma_71_6_11_WeaklyAssociated
public import stacks_project.Chap71.Definition_71_10_6_Pullback

/-!
# Lemma 71.10.7

Pullbacks of meromorphic sections along a morphism of algebraic spaces are defined
when weakly associated points of the source map to codimension-`0` points of the
target, or when the morphism is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 71.10.7 (1): for a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, if every weakly associated point of `X` is mapped to a point of
codimension `0` on `Y`, then pullbacks of meromorphic sections are defined. -/
@[stacks 0EN9]
theorem pullbacksMeromorphicFunctionsDefined_of_weakAss_mapsTo_codimZero
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hweak : Set.MapsTo (Points.map f) X.weakAss (codimZeroPoints Y)) :
    PullbacksMeromorphicFunctionsDefined f :=
  sorry

/-- Lemma 71.10.7 (2): pullbacks of meromorphic sections are defined for a
flat morphism of algebraic spaces. -/
@[stacks 0EN9]
instance instPullbacksMeromorphicFunctionsDefined_of_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [Flat f] :
    PullbacksMeromorphicFunctionsDefined f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
