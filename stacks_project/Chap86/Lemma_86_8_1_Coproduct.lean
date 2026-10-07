module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_5_3_Coproducts
public import stacks_project.Chap86.«86_3_2_1_Pushforward»

/-!
# Coproduct preservation for the right adjoint of proper flat pushforward

Any right adjoint of restricted derived pushforward along a proper, flat, finitely
presented morphism of algebraic spaces with quasi-compact quasi-separated target
preserves arbitrary direct sums.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- Any right adjoint to derived quasicoherent pushforward along a proper, flat,
finite-presentation morphism of algebraic spaces with quasi-compact
quasi-separated target preserves coproducts. -/
theorem rightAdjoint_preservesCoproducts_of_proper_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (I : Type u) :
    PreservesColimitsOfShape (Discrete I) a :=
  sorry

/-- The comparison morphism `∐ a.obj (K i) ⟶ a.obj (∐ K)` is an isomorphism for any
right adjoint as in `rightAdjoint_preservesCoproducts_of_proper_flat`. -/
theorem rightAdjoint_sigmaComparison_isIso_of_proper_flat
    {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) [Proper f] [Flat f] [FinitePresentation f]
    (a : DerivedQCoh Y ⥤ DerivedQCoh X) (aAdjunction : pushforwardCohomologyIn f ⊣ a)
    (I : Type u) (K : I → DerivedQCoh Y) :
    IsIso (sigmaComparison a K) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
