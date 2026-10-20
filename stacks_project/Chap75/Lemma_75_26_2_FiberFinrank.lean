/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Semicontinuity.Defs
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap75.Lemma_75_3_1_Pushforward
public import stacks_project.Chap75.Lemma_75_26_3_FiberEulerCharacteristic

/-!
# Fiber cohomology finrank along a morphism of algebraic spaces

The function recording `dim_{κ(y)} H^i(X_y, ℱ_y)` is realized as the fiber Betti
function of `Rf_* (ℱ[0])`, after identifying scheme points of the base with points
of the associated algebraic space.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The degree-`i` fiber cohomology finrank of `ℱ` along `f`, sending a point of the
base scheme to `dim_{κ(t)} H^i(X_t, ℱ_t)`, computed as the fiber Betti number of
`Rf_* (ℱ[0])`. -/
noncomputable def fiberCohomologyFinrank {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    {T : Over Y} (f : X ⟶ ofOver T) (ℱ : X.Modules) (i : ℤ) : T.left → ℕ :=
  fun t ↦ ModuleDerived.fiberBetti
    ((Modules.pushforwardDerived f).obj ((DerivedCategory.singleFunctor (Modules X) 0).obj ℱ))
    i (ofOver.pointsEquiv T t)

/-- The fiber cohomology finrank at a point is the fiber Betti number of the derived
pushforward of `ℱ` placed in degree zero. -/
theorem fiberCohomologyFinrank_apply {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    {T : Over Y} (f : X ⟶ ofOver T) (ℱ : X.Modules) (i : ℤ) (t : T.left) :
    fiberCohomologyFinrank f ℱ i t =
      ModuleDerived.fiberBetti
        ((Modules.pushforwardDerived f).obj
          ((DerivedCategory.singleFunctor (Modules X) 0).obj ℱ))
        i (ofOver.pointsEquiv T t) :=
  sorry

/-- Unfold the fiber cohomology finrank as a function of scheme points. -/
theorem fiberCohomologyFinrank_def {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    {T : Over Y} (f : X ⟶ ofOver T) (ℱ : X.Modules) (i : ℤ) :
    fiberCohomologyFinrank f ℱ i =
      fun t ↦ ModuleDerived.fiberBetti
        ((Modules.pushforwardDerived f).obj
          ((DerivedCategory.singleFunctor (Modules X) 0).obj ℱ))
        i (ofOver.pointsEquiv T t) :=
  sorry

/-- The fiber cohomology finrank is the fiber Betti function of `Rf_* (ℱ[0])`,
precomposed with the identification of scheme points with algebraic-space points. -/
theorem fiberCohomologyFinrank_eq_pushforwardFiberBetti {Y : Scheme.{u}}
    {X : AlgebraicSpace Y} {T : Over Y} (f : X ⟶ ofOver T) (ℱ : X.Modules) (i : ℤ) :
    fiberCohomologyFinrank f ℱ i =
      ModuleDerived.fiberBetti
        ((Modules.pushforwardDerived f).obj
          ((DerivedCategory.singleFunctor (Modules X) 0).obj ℱ))
        i ∘ ofOver.pointsEquiv T :=
  sorry

/-- Formation of the fiber cohomology finrank commutes with arbitrary cartesian base
change of algebraic spaces over `Y`. -/
theorem fiberCohomologyFinrank_baseChange {Y : Scheme.{u}} {X X' : AlgebraicSpace Y}
    {T : Over Y} (g' : X' ⟶ X) (f' : X' ⟶ ofOver T)
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (g : ofOver T ⟶ ofOver (Over.mk (𝟙 Y)))
    [Flat f] [Proper f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (hℱ_flat : Modules.flatOver ℱ f) (sq : IsPullback g' f' f g) (i : ℤ) :
    fiberCohomologyFinrank f' ((Modules.pullback g').obj ℱ) i =
      fun t ↦ fiberCohomologyFinrank f ℱ i (T.hom t) :=
  sorry

/-- The fiber cohomology finrank after cartesian base change is the original value at
the image point of the base. -/
theorem fiberCohomologyFinrank_baseChange_apply {Y : Scheme.{u}}
    {X X' : AlgebraicSpace Y} {T : Over Y} (g' : X' ⟶ X) (f' : X' ⟶ ofOver T)
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) (g : ofOver T ⟶ ofOver (Over.mk (𝟙 Y)))
    [Flat f] [Proper f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (hℱ_flat : Modules.flatOver ℱ f) (sq : IsPullback g' f' f g) (i : ℤ) (t : T.left) :
    fiberCohomologyFinrank f' ((Modules.pullback g').obj ℱ) i t =
      fiberCohomologyFinrank f ℱ i (T.hom t) :=
  sorry

/-- Every fiber cohomology finrank function of a finitely presented module, flat over
the base, along a flat proper morphism of finite presentation, is upper
semicontinuous. -/
theorem fiberCohomologyFinrank_upperSemicontinuous {Y : Scheme.{u}}
    {X : AlgebraicSpace Y} (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Flat f] [Proper f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (hℱ_flat : Modules.flatOver ℱ f) (i : ℤ) :
    UpperSemicontinuous (fiberCohomologyFinrank f ℱ i) :=
  sorry

/-- Every level set of a fiber cohomology finrank function of a finitely presented
module, flat over the base, along a flat proper morphism of finite presentation, is
locally constructible in `Y`. -/
theorem fiberCohomologyFinrank_levelSet_isLocallyConstructible {Y : Scheme.{u}}
    {X : AlgebraicSpace Y} (f : X ⟶ ofOver (Over.mk (𝟙 Y)))
    [Flat f] [Proper f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (hℱ_flat : Modules.flatOver ℱ f) (i : ℤ) (n : ℕ) :
    Topology.IsLocallyConstructible ((fiberCohomologyFinrank f ℱ i) ⁻¹' {n}) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
