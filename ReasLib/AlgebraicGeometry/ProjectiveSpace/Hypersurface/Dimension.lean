/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Hypersurface
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Topology.KrullDimension

/-!
# Dimension of smooth projective hypersurfaces
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.ProjectiveSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace.Hypersurface

/-- A nonempty smooth hypersurface of positive degree in `ℙ^3` has topological Krull dimension
`2`. -/
theorem hypersurface_topologicalKrullDim_eq_two {k : Type u} [Field k]
    (d : ℕ) (F : MvPolynomial (Fin (3 + 1)) k) (hF : F ∈ grading k 3 d)
    (hFne : F ≠ 0) (hd : 0 < d) [Smooth (hom 3 d F hF)] :
    topologicalKrullDim (⊥ : (scheme 3 d F hF).IdealSheafData).subscheme = (2 : ℕ) := sorry

end AlgebraicGeometry.ProjectiveSpace.Hypersurface
