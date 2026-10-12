/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Remark_75_9_5_AffineDiagonal
public import stacks_project.Chap67.Lemma_67_8_10_Instances
public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import stacks_project.Chap75.«75_5_1_1_Comparison»
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Comparison of derived quasi-coherent pushforward on quasi-compact algebraic spaces
with affine diagonal

For a morphism of quasi-compact algebraic spaces with affine diagonal over the
terminal scheme, the K-injective right-derived quasi-coherent pushforward is
compatible with restricted ambient derived pushforward after the canonical
comparisons `D(QCoh) ⥤ D_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a morphism of quasi-compact algebraic spaces with affine diagonal over the
terminal scheme, the K-injective right-derived quasi-coherent pushforward and
restricted ambient derived pushforward agree after applying the canonical
comparisons `DerivedCategory (QCoh _) ⥤ DerivedQCoh _`. -/
theorem pushforwardComparison_isomorphic_of_compact_affineDiagonal {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsQuasiCompact X] [IsQuasiCompact Y]
    [IsAbsolutelyAffineDiagonal X] [IsAbsolutelyAffineDiagonal Y] :
    IsIsomorphic (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforward f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
