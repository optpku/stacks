/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Automorphism
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus

/-!
# Dimensions of automorphism groups of genus-zero and genus-one curves
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k)
variable [Curve X] [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom]

/-- Over an algebraically closed field, a representing scheme of `autFunctor X` for a
smooth projective geometrically irreducible genus-zero curve `X` has topological Krull
dimension `3`. -/
theorem aut_topologicalKrullDim_eq_three_of_genus_zero
    (h_genus : Curve.genus X = 0) (G : SchemeOverField k)
    (hG : (autFunctor X ⋙ forget GrpCat).RepresentableBy G) :
    topologicalKrullDim G.left = 3 := sorry

/-- Over an algebraically closed field, a representing scheme of `autFunctor X` for a
smooth projective geometrically irreducible genus-one curve `X` has topological Krull
dimension `1`. -/
theorem aut_topologicalKrullDim_eq_one_of_genus_one
    (h_genus : Curve.genus X = 1) (G : SchemeOverField k)
    (hG : (autFunctor X ⋙ forget GrpCat).RepresentableBy G) :
    topologicalKrullDim G.left = 1 := sorry

end AlgebraicGeometry.SchemeOverField
