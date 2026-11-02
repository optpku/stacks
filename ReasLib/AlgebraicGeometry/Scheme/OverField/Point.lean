/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- The spectrum of `k`, represented by the terminal scheme over `k`. -/
def point (k : Type u) [Field k] : SchemeOverField k :=
  ⊤_ (SchemeOverField k)

/-- The structure morphism of `point k` is an isomorphism to `Spec k`. -/
instance pointHomIsIso (k : Type u) [Field k] : IsIso (point k).hom := by
  let e : point k ≅ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
    terminalIsTerminal.uniqueUpToIso Over.mkIdTerminal
  have h : e.hom.left = (point k).hom := by
    simpa only [Category.comp_id] using! e.hom.w
  rw [← h]
  change IsIso ((Over.forget _).map e.hom)
  infer_instance

/-- The chosen spectrum of a field is terminal among schemes over that field. -/
def pointIsTerminal (k : Type u) [Field k] : IsTerminal (point k) :=
  terminalIsTerminal

/-- The canonical comparison between the field point and the chosen terminal object. -/
def pointIsoTerminal (k : Type u) [Field k] :
    point k ≅ ⊤_ (SchemeOverField k) :=
  Iso.refl _

end AlgebraicGeometry.SchemeOverField
