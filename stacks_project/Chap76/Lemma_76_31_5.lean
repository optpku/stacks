module

public import Mathlib.Topology.LocallyConstant.Basic
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap76.Lemma_76_31_1_FiberDimension

/-!
# Local constancy of fibre dimensions of proper flat morphisms of algebraic spaces

The target-indexed fibre dimension of a proper, flat, finitely presented morphism of
algebraic spaces is locally constant on the space of points of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Topology

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 76.31.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a proper, flat,
finitely presented morphism of algebraic spaces over `S`. Let `fiberDimension f`
be the function on `Points Y` giving the dimension of fibres of `f` introduced
in Lemma 76.31.2. Then `fiberDimension f` is locally constant. -/
@[stacks 0D4R]
theorem isLocallyConstant_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f] :
    IsLocallyConstant (fiberDimension f) :=
  sorry

/-- The fibre-dimension function of a proper, flat, finitely presented morphism of
algebraic spaces is locally constant at a point of the target. -/
theorem eventually_eq_fiberDimension {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (y : Points Y) :
    ∀ᶠ y' in 𝓝 y, fiberDimension f y' = fiberDimension f y :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
