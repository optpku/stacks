/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap86.«86_7_0_1_Comparison»

/-!
# Invertibility of the duality comparison for proper flat morphisms

For a proper, flat, finitely presented morphism of algebraic spaces with
quasi-compact quasi-separated target, the canonical comparison
`Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` is an isomorphism for every derived quasicoherent object.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a proper, flat, finitely presented morphism of algebraic spaces with
quasi-compact quasi-separated target, the comparison `Lf^*K ⊗^L a(𝒪_Y) ⟶ a(K)` is an
isomorphism for every derived quasicoherent `K`. -/
theorem pullbackTensorDualityMap_isIso_of_proper_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (K : DerivedQCoh Y) :
    IsIso (pullbackTensorDualityMap f a aAdjunction K) :=
  sorry

/-- The duality comparison natural transformation is an isomorphism under the same
proper, flat, finite-presentation hypotheses. -/
theorem pullbackTensorDualityNatTrans_isIso_of_proper_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a) :
    IsIso (pullbackTensorDualityNatTrans f a aAdjunction) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
