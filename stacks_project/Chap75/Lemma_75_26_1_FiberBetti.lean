/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Semicontinuity.Defs
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap66.Lemma_66_8_1_Constructible
public import stacks_project.Chap75.Lemma_75_13_6_PseudoCoherent
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic
public import stacks_project.Chap75.Lemma_75_26_6_Pullback

/-!
# Fiber Betti functions of pseudo-coherent complexes on algebraic spaces

Degreewise fiber Betti numbers of a pseudo-coherent derived module on an algebraic space
commute with arbitrary base change, are upper semicontinuous, and have étale-locally
constructible level sets.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Isomorphic derived modules have the same degreewise fiber Betti functions. -/
theorem fiberBetti_eq_of_iso {E F : ModuleDerived X} (e : E ≅ F) (i : ℤ) :
    fiberBetti E i = fiberBetti F i := sorry

/-- A pseudo-coherent derived module has finite-dimensional residue-field fiber cohomology in
every degree. -/
theorem fiberCohomology_finiteDimensional_of_isPseudoCoherent
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E) (xbar : GeometricPoint X) (i : ℤ) :
    FiniteDimensional (IsLocalRing.ResidueField (etaleLocalRing X xbar))
      (fiberHomology E xbar i) := sorry

/-- Formation of the degreewise fiber Betti function of a pseudo-coherent derived module
commutes with arbitrary base change of algebraic spaces. -/
theorem fiberBetti_pullback {Y : AlgebraicSpace S} (f : Y ⟶ X) (E : ModuleDerived X)
    (hE : IsPseudoCoherent X E) (i : ℤ) :
    fiberBetti ((pullback f).obj E) i = fun y ↦ fiberBetti E i (Points.map f y) :=
  sorry

/-- The degreewise fiber Betti number after derived pullback is the original Betti number at
the image point. -/
theorem fiberBetti_pullback_apply {Y : AlgebraicSpace S} (f : Y ⟶ X)
    (E : ModuleDerived X) (hE : IsPseudoCoherent X E) (i : ℤ) (y : Points Y) :
    fiberBetti ((pullback f).obj E) i y = fiberBetti E i (Points.map f y) :=
  sorry

/-- Every degreewise fiber Betti function of a pseudo-coherent derived module is upper
semicontinuous. -/
theorem fiberBetti_upperSemicontinuous (E : ModuleDerived X) (hE : IsPseudoCoherent X E)
    (i : ℤ) :
    UpperSemicontinuous (fiberBetti E i) := sorry

/-- Every level set of a degreewise fiber Betti function of a pseudo-coherent derived module is
étale locally constructible. -/
theorem fiberBetti_levelSet_isEtaleLocallyConstructible (E : ModuleDerived X)
    (hE : IsPseudoCoherent X E) (i : ℤ) (n : ℕ) :
    IsEtaleLocallyConstructible ((fiberBetti E i) ⁻¹' {n}) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
