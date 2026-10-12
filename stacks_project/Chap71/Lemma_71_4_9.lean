/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap71.Lemma_71_4_6_RelativeAssassin

/-!
# Lemma 71.4.9

The relative weak assassin of a quasi-coherent module is preserved by
pushforward along a finite morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- Lemma 71.4.9: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Let `i : Z ⟶ X` be a finite morphism. Let `G` be a
quasi-coherent `𝒪_Z`-module. Then
`relativeWeakAss f ((pushforward i).obj G) =
  Points.map i '' relativeWeakAss (i ≫ f) G`. -/
@[stacks 0CV4]
theorem relativeWeakAss_pushforward_eq_image_of_isFinite
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (i : Z ⟶ X)
    [IsFinite i] (G : Z.Modules) [G.IsQuasicoherent] :
    relativeWeakAss f ((pushforward i).obj G) =
      Points.map i '' relativeWeakAss (i ≫ f) G :=
  sorry

/-- A point of `|X|` is relatively weakly associated to the finite pushforward of
a quasi-coherent module if and only if it is the image of a point relatively
weakly associated to that module over `Y`. -/
theorem mem_relativeWeakAss_pushforward_iff_of_isFinite
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (i : Z ⟶ X)
    [IsFinite i] (G : Z.Modules) [G.IsQuasicoherent] (x : Points X) :
    x ∈ relativeWeakAss f ((pushforward i).obj G) ↔
      ∃ z : Points Z, z ∈ relativeWeakAss (i ≫ f) G ∧ Points.map i z = x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
