/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Fiber
public import ReasLib.CategoryTheory.MonoidalCategory.TensorPower

/-! # Fibre ampleness and eventual stalk cohomology -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- For a proper algebraic space over a Noetherian scheme, an invertible module ample
on a scheme fibre makes every coherent twist eventually have vanishing positive
higher-direct-image stalks at that point and a surjective canonical degree-zero
stalk-to-fibre map, with a common bound for both conclusions. -/
theorem exists_twist_stalk_isZero_and_surjective_of_isAmple_fiber
    {Y : Scheme.{u}} [IsNoetherian Y] {X : AlgebraicSpace Y}
    (f : X ⟶ ofOver (Over.mk (𝟙 Y))) [Proper f]
    [Abelian X.Modules] [Abelian (ofOver (Over.mk (𝟙 Y))).Modules]
    [HasInjectiveResolutions X.Modules]
    (L : X.Modules) [isInvertibleObject L] (F : X.Modules) [F.IsCoherent] (y : Y)
    {T : Over Y} (e : fiber f y ≅ ofOver T)
    [Scheme.Modules.IsAmple (moduleOnScheme f y e L)] :
    ∃ d0 : ℕ, ∀ d, d0 ≤ d →
      (∀ p, 0 < p →
          IsZero (RingedSpace.stalkModuleCat
            (higherDirectImageOnScheme f (F ⊗ tensorPower L d) p) y)) ∧
        Function.Surjective
          (ConcreteCategory.hom
            (pushforwardStalkToFiberCohomology f (F ⊗ tensorPower L d) y e)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
