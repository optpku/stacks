/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Semicontinuity.Defs
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_31_1_FiberDimension

/-!
# Lower semicontinuity of fibre dimensions of flat morphisms of algebraic spaces

The target-indexed fibre dimension of a flat morphism of finite presentation of
algebraic spaces is lower semicontinuous on the space of points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.31.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
finite presentation of algebraic spaces over `S`. Let `fiberDimension f` be the
function on `Points Y` giving the dimension of fibres of `f` introduced in
Lemma 76.31.2. Then `fiberDimension f` is lower semicontinuous. -/
@[stacks 0D4P]
theorem lowerSemicontinuous_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [FinitePresentation f] :
    LowerSemicontinuous (fiberDimension f) :=
  sorry

/-- The fibre-dimension function of a flat finite-presentation morphism of
algebraic spaces is lower semicontinuous at a point of the target. -/
theorem lowerSemicontinuousAt_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Flat f] [FinitePresentation f]
    (y : Points Y) :
    LowerSemicontinuousAt (fiberDimension f) y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
