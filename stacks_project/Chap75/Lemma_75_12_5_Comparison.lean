/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import stacks_project.Chap75.«75_5_1_1_Comparison»
public import stacks_project.Chap75.Lemma_75_6_1_Pushforward

/-!
# Comparison of derived quasi-coherent pushforward on Noetherian algebraic spaces

For a morphism of Noetherian algebraic spaces, the K-injective right-derived
quasi-coherent pushforward is compatible with restricted ambient derived
pushforward after the canonical comparisons `D(QCoh) ⥤ D_QCoh`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a morphism of Noetherian algebraic spaces, the K-injective right-derived
quasi-coherent pushforward and restricted ambient derived pushforward agree after
applying the canonical comparisons `DerivedCategory (QCoh _) ⥤ DerivedQCoh _`. -/
theorem pushforwardComparison_isomorphic {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsNoetherian X] [IsNoetherian Y]
    [QuasiCompact f] [QuasiSeparated f] :
    IsIsomorphic (QCoh.Derived.pushforward f ⋙ comparison Y)
      (comparison X ⋙ pushforward f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
