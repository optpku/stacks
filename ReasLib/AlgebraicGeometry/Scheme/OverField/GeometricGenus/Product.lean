module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.IrreducibleCriteria
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.GeometricGenus
public import ReasLib.CategoryTheory.Limits.Over.Products

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- A curve closed in a product of smooth projective curves has geometric genus at least
`2 * g + 1` when the factor genera are `g` and `g + 1` and both projections are nonconstant. -/
theorem geometricGenus_ge_two_mul_add_one
    {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ} (hg : 3 ≤ g)
    (X X' : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom]
    [Curve X'] [Projective X'.hom] [Smooth X'.hom]
    (hX : genus X = g) (hX' : genus X' = g + 1)
    (Y : SchemeOverField k) [Curve Y]
    (ι : Y ⟶ X ⨯ X') [IsClosedImmersion ι.left]
    (h_fst : (ι ≫ prod.fst).left.IsNonconstant)
    (h_snd : (ι ≫ prod.snd).left.IsNonconstant) :
    2 * g + 1 ≤ geometricGenus Y := sorry

/-- A nonsingular projective model of a curve closed in a product of smooth projective curves
has genus at least `2 * g + 1` under the corresponding genus and projection hypotheses. -/
theorem nonsingularProjectiveModel_genus_ge
    {k : Type u} [Field k] [IsAlgClosed k] {g : ℕ} (hg : 3 ≤ g)
    (X X' : SchemeOverField k)
    [Curve X] [Projective X.hom] [Smooth X.hom]
    [Curve X'] [Projective X'.hom] [Smooth X'.hom]
    (hX : genus X = g) (hX' : genus X' = g + 1)
    (Y : SchemeOverField k) [Curve Y]
    (ι : Y ⟶ X ⨯ X') [IsClosedImmersion ι.left]
    (h_fst : (ι ≫ prod.fst).left.IsNonconstant)
    (h_snd : (ι ≫ prod.snd).left.IsNonconstant)
    (M : NonsingularProjectiveModel.WithIso Y) :
    2 * g + 1 ≤ M.genus := sorry

end AlgebraicGeometry.Curve
