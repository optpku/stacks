/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme.CoordinateIdeal
public import ReasLib.AlgebraicGeometry.Scheme.EmbeddedPoints
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

@[expose] public section

open CategoryTheory Set TopologicalSpace

universe u

namespace AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme

/-- A nonempty equidimensional one-dimensional closed subscheme of the projective plane
without embedded points is a curve exactly when its homogeneous coordinate generator is
irreducible. -/
theorem curve_iff_irreducible_generator
    (k : Type u) [Field k]
    (Z : (ProjectiveSpace.scheme k 2).IdealSheafData)
    [Nonempty Z.subscheme]
    (h_componentDim : ∀ C : irreducibleComponents Z.subscheme,
      topologicalKrullDim (C : Set Z.subscheme) = 1)
    (h_noEmbeddedPoints : Z.subscheme.embeddedPoints = (∅ : Set Z.subscheme))
    (F : MvPolynomial (Fin 3) k)
    (h_generator : coordinateIdeal 2 Z = Ideal.span {F}) :
    Curve (Over.mk (Z.subschemeι ≫ ProjectiveSpace.toSpec k 2)) ↔ Irreducible F := sorry

end AlgebraicGeometry.ProjectiveSpace.ClosedSubscheme
