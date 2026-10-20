/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionMultiplicity

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The local intersection multiplicity at every irreducible component of a proper
intersection of closed subvarieties in a regular variety is strictly positive. -/
theorem intersectionMultiplicity_pos
    {k : Type u} [Field k] (X : SchemeOverField k) [Variety X]
    [Scheme.Regular X.left] (V W : X.left.IdealSheafData)
    [Variety (Over.mk (V.subschemeι ≫ X.hom))]
    [Variety (Over.mk (W.subschemeι ≫ X.hom))]
    (hproper : Closeds.IntersectProperly V.support W.support)
    (Z : irreducibleComponents (V ⊔ W).subscheme) :
    0 < V.intersectionMultiplicity W (genericPoints.ofComponent Z) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
