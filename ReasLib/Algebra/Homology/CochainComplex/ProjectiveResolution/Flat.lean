/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.ProjectiveResolution.Basic
public import ReasLib.Algebra.Homology.HomologicalComplex.Flat.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flatness of projective-minus module complexes

This leaf exposes the module-theoretic flatness consequence of the categorical projectivity
already bundled by `CochainComplex.ProjectiveMinus`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace CochainComplex.ProjectiveMinus

variable {R : Type u} [CommRing R]

/-- Stacks `0643`: the underlying module complex of a projective-minus object is termwise flat. -/
@[stacks 0643 "termwise flatness of a projective-minus complex"]
theorem termwiseFlat (P : CochainComplex.ProjectiveMinus (ModuleCat R)) :
    HomologicalComplex.IsTermwiseFlat (P : CochainComplex (ModuleCat R) ℤ) := sorry

end CochainComplex.ProjectiveMinus

end
