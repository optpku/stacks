/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Semicontinuity.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pushforward
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.FiberEulerCharacteristic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.OverAffine

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
    ((Modules.moduleDerivedPushforward f).obj ((DerivedCategory.singleFunctor (Modules X) 0).obj ℱ))
    i (ofOver.pointsEquiv T t)

/-- The fiber cohomology finrank at a point is the fiber Betti number of the derived
pushforward of `ℱ` placed in degree zero. -/
theorem fiberCohomologyFinrank_apply {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    {T : Over Y} (f : X ⟶ ofOver T) (ℱ : X.Modules) (i : ℤ) (t : T.left) :
    fiberCohomologyFinrank f ℱ i t =
      ModuleDerived.fiberBetti
        ((Modules.moduleDerivedPushforward f).obj
          ((DerivedCategory.singleFunctor (Modules X) 0).obj ℱ))
        i (ofOver.pointsEquiv T t) :=
  rfl

/-- The fiber cohomology finrank is the fiber Betti function of `Rf_* (ℱ[0])`,
precomposed with the identification of scheme points with algebraic-space points. -/
theorem fiberCohomologyFinrank_eq_pushforwardFiberBetti {Y : Scheme.{u}}
    {X : AlgebraicSpace Y} {T : Over Y} (f : X ⟶ ofOver T) (ℱ : X.Modules) (i : ℤ) :
    fiberCohomologyFinrank f ℱ i =
      ModuleDerived.fiberBetti
        ((Modules.moduleDerivedPushforward f).obj
          ((DerivedCategory.singleFunctor (Modules X) 0).obj ℱ))
        i ∘ ofOver.pointsEquiv T :=
  rfl

/-- The cohomology of the canonical residue-field fiber of a finitely presented module,
flat over the base, along a flat proper finitely presented morphism is finite-dimensional. -/
theorem fiberCohomology_finiteDimensional {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    {T : Over Y} (f : X ⟶ ofOver T)
    [Flat f] [Proper f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (hℱ_flat : Modules.flatOver ℱ f) (t : T.left) (n : ℕ) :
    let σ := T.left.fromSpecResidueField t ≫ T.hom
    let a : ofOver (Over.mk σ) ⟶ ofOver T :=
      ofOverMap (Over.homMk (T.left.fromSpecResidueField t) rfl)
    FiniteDimensional (T.left.residueField t)
      (Modules.cohomologyOver (A := T.left.residueField t) σ (pullback.snd f a)
        ((Modules.pullback (pullback.fst f a)).obj ℱ) n) :=
  sorry

/-- For a finitely presented module flat over the base of a flat proper finitely presented
morphism, the fiber cohomology finrank is the dimension of ordinary residue-field fiber
cohomology in nonnegative degrees and is zero in negative degrees. -/
theorem fiberCohomologyFinrank_eq_cohomologyOver {Y : Scheme.{u}} {X : AlgebraicSpace Y}
    {T : Over Y} (f : X ⟶ ofOver T)
    [Flat f] [Proper f] [FinitePresentation f] (ℱ : X.Modules) [ℱ.IsFinitePresentation]
    (hℱ_flat : Modules.flatOver ℱ f) (i : ℤ) (t : T.left) :
    let σ := T.left.fromSpecResidueField t ≫ T.hom
    let a : ofOver (Over.mk σ) ⟶ ofOver T :=
      ofOverMap (Over.homMk (T.left.fromSpecResidueField t) rfl)
    fiberCohomologyFinrank f ℱ i t =
      if 0 ≤ i then
        Module.finrank (T.left.residueField t)
          (Modules.cohomologyOver (A := T.left.residueField t) σ (pullback.snd f a)
            ((Modules.pullback (pullback.fst f a)).obj ℱ) i.toNat)
      else 0 :=
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
  congrFun (fiberCohomologyFinrank_baseChange g' f' f g ℱ hℱ_flat sq i) t

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
