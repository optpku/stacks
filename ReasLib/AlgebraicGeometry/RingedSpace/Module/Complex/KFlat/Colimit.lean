/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Complex.KFlat.Colimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential colimits of K-flat complexes on ringed spaces

@stack 06YE

The ringed-site colimit owner specializes directly to the opens ringed site of a ringed space.
No tensor, additive, or colimit witnesses belong in the source-facing theorem.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat

variable {X : RingedSpace.{u}}

/-- Lemma 20.26.10 (06YE): sequential colimits of K-flat complexes of `𝒪_X`-modules are K-flat. -/
@[stacks 06YE "sequential colimits preserve K-flatness"]
theorem sequentialColimit
    (F : ℕ ⥤ CochainComplex (Modules X) ℤ)
    (hF : ∀ i, (F.obj i).IsKFlat) :
    (colimit F).IsKFlat := sorry

end AlgebraicGeometry.RingedSpace.CochainComplex.IsKFlat

end
