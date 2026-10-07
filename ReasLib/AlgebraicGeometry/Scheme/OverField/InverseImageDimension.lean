module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalCompleteIntersection.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety

/-!
# Dimension of inverse images over a field

This file gives lower bounds for the dimensions of irreducible components of
scheme-theoretic inverse images under regular immersions and local complete-intersection
morphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- If a regular immersion of varieties has conormal rank `c`, then every irreducible
component of the scheme-theoretic inverse image of a `d`-dimensional closed integral
subscheme has dimension at least `d - c`. -/
theorem componentDimension_lowerBound_of_regularImmersion
    {k : Type u} [Field k] {X Y : SchemeOverField k} [Variety X] [Variety Y]
    (f : X ⟶ Y) (Z : Y.left.IdealSheafData)
    [Variety (Over.mk (Z.subschemeι ≫ Y.hom))]
    (d c : ℕ) (hZ : topologicalKrullDim Z.subscheme = (d : WithBot ℕ∞))
    [IsRegularImmersion f.left]
    [Scheme.Modules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf f.left)]
    (C : irreducibleComponents (Z.comap f.left).subscheme) :
    ((d - c : ℕ) : WithBot ℕ∞) ≤
      topologicalKrullDim C := sorry

/-- If a local complete-intersection morphism of varieties has virtual relative dimension
`r`, then every irreducible component of the scheme-theoretic inverse image of a
`d`-dimensional closed integral subscheme has dimension at least `d + r`. -/
theorem componentDimension_lowerBound_of_localCompleteIntersection
    {k : Type u} [Field k] {X Y : SchemeOverField k} [Variety X] [Variety Y]
    (f : X ⟶ Y) (Z : Y.left.IdealSheafData)
    [Variety (Over.mk (Z.subschemeι ≫ Y.hom))]
    (d : ℕ) (r : ℤ) (hZ : topologicalKrullDim Z.subscheme = (d : WithBot ℕ∞))
    (h_lci : LocalCompleteIntersectionOfRelativeDimension f.left r)
    (C : irreducibleComponents (Z.comap f.left).subscheme) :
    (Int.toNat ((d : ℤ) + r) : WithBot ℕ∞) ≤
      topologicalKrullDim C := sorry

end AlgebraicGeometry.SchemeOverField
