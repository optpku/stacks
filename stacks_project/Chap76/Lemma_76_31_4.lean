/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Semicontinuity.Defs
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_53_4_UniversalHomeomorphism
public import stacks_project.Chap76.Lemma_76_31_1_FiberDimension

/-!
# Upper semicontinuity of fibre dimensions

For a proper morphism of algebraic spaces, the target-indexed fibre-dimension
function is upper semi-continuous on the canonical topology of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.31.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper morphism
of algebraic spaces over `S`. Let `fiberDimension f` be the function on
`Points Y` giving the dimension of fibres of `f` introduced in
Lemma 76.31.2. Then `fiberDimension f` is upper semi-continuous. -/
@[stacks 0D4Q]
theorem upperSemicontinuous_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f]
    {τ : TopologicalSpace (Points Y)} (hτ : IsPointsTopology Y τ) :
    @UpperSemicontinuous (Points Y) (WithBot ℕ∞) τ inferInstance
      (fiberDimension f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
