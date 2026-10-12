/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Constructible
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap71.Lemma_71_15_2_Fiber
public import stacks_project.Chap71.Lemma_71_2_1_WeakAss

/-!
# Lemma 71.4.10

The locus of points of a scheme `Y` at which the associated points of a
finitely presented module on a finite-presentation algebraic space over `Y`
lie in a quasi-compact open subspace is locally constructible.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus of points of `Y` at which the associated points of the residue-field
fibre module lie in the fibre of an open subspace. -/
def associatedPointsFiberSubset {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (F : X.Modules) (U : OpenSubspace X) : Set Y :=
  setOf fun y : Y ↦
    (setOf fun x : Points (AlgebraicSpace.fiber f y) ↦
        existsEtaleAss ((pullback (AlgebraicSpace.fiberι f y)).obj F) x) ⊆
      Points.map (AlgebraicSpace.fiberι f y) ⁻¹' U.pointsSet

/-- Membership in `associatedPointsFiberSubset` is the fibrewise associated-point
inclusion of `Ass` of the residue-field fibre module into the fibre of `U`. -/
theorem mem_associatedPointsFiberSubset_iff {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (F : X.Modules) (U : OpenSubspace X) (y : Y) :
    y ∈ associatedPointsFiberSubset f F U ↔
      (setOf fun x : Points (AlgebraicSpace.fiber f y) ↦
          existsEtaleAss ((pullback (AlgebraicSpace.fiberι f y)).obj F) x) ⊆
        Points.map (AlgebraicSpace.fiberι f y) ⁻¹' U.pointsSet :=
  sorry

/-- Lemma 71.4.10: Let `Y` be a scheme. Let `X` be an algebraic space of finite
presentation over `Y`. Let `F` be a quasi-coherent `𝒪_X`-module of finite
presentation. Let `U ⊂ X` be an open subspace such that `U → Y` is quasi-compact.
Then `E = {y ∈ Y | Ass_{X_y}(F_y) ⊆ |U_y|}` is locally constructible in `Y`. -/
@[stacks 0CVV]
theorem associatedPoints_fiber_subset_isLocallyConstructible
    {Y : Scheme.{u}} {X : AlgebraicSpace Y} (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [FinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (U : OpenSubspace X) [QuasiCompact (U.ι ≫ f)] :
    Topology.IsLocallyConstructible (associatedPointsFiberSubset f F U) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
