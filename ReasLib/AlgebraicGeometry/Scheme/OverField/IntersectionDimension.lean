/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.InverseImageDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Dimension
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Diagonal

/-!
# Dimension of intersections over a field

This file gives lower bounds for the dimensions of irreducible components of
scheme-theoretic intersections of closed subvarieties of regular varieties.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- Every irreducible component of the scheme-theoretic intersection of two closed
subvarieties of a regular variety has dimension at least the sum of their dimensions
minus the dimension of the ambient variety. -/
theorem componentDimension_lowerBound_of_intersection
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Variety X] [Scheme.Regular X.left]
    (V W : X.left.IdealSheafData)
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    [Variety (Over.mk (W.subschemeι ≫ X.hom))]
    (r s : ℕ)
    (hV : topologicalKrullDim V.subscheme = (r : WithBot ℕ∞))
    (hW : topologicalKrullDim W.subscheme = (s : WithBot ℕ∞))
    (Z : irreducibleComponents (V ⊔ W).subscheme) :
    ((r + s - baseFieldTrdegAt X (genericPoint X.left) : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDim Z := sorry

end AlgebraicGeometry.SchemeOverField
