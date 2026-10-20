/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Algebra.Ring.Real
public import ReasLib.Topology.Sheaves.ContinuousFunctions.Algebra

/-!
# Sheaf of continuous real-valued functions

This module specializes the generic `CommAlgCat`-valued continuous-functions construction to
`ℝ`.  The generic owner is `Topology.Sheaves.ContinuousFunctions.Algebra`; these names retain the
standard real-valued presentation used by geometry applications.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

noncomputable section

universe v

namespace TopCat.ContinuousFunctions.Real

/-- The presheaf of continuous real-valued functions, viewed as a presheaf of `ℝ`-algebras. -/
abbrev presheaf (X : TopCat.{v}) : X.Presheaf (CommAlgCat.{v} ℝ) :=
  ContinuousFunctions.presheaf ℝ X

/-- The sheaf of continuous real-valued functions, carried as a sheaf of `ℝ`-algebras. -/
abbrev sheaf (X : TopCat.{v}) : X.Sheaf (CommAlgCat.{v} ℝ) :=
  ContinuousFunctions.sheaf ℝ X

/-- Pullback of continuous real-valued functions along a continuous map. -/
abbrev pushforwardMap {X Y : TopCat.{v}} (f : X ⟶ Y) :
    sheaf Y ⟶ (TopCat.Sheaf.pushforward (CommAlgCat.{v} ℝ) f).obj (sheaf X) :=
  ContinuousFunctions.pushforwardMap ℝ f

/-- The component of `pushforwardMap f` over `V` is precomposition with the restriction of `f`
to `f ⁻¹' V`. -/
theorem pushforwardMap_app {X Y : TopCat.{v}} (f : X ⟶ Y)
    (V : (Opens Y)ᵒᵖ) :
    (pushforwardMap f).1.app V =
      CommAlgCat.ofHom
        (ContinuousMap.compRightAlgHom ℝ ℝ
          (f.hom.restrictPreimage (V.unop : Set Y))) := sorry

end TopCat.ContinuousFunctions.Real
