module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.OpenExtension
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Curve

/-- A morphism from a nonempty open subscheme of a curve to a proper variety extends over an
open neighbourhood of a closed point whose local ring is a discrete valuation ring. -/
theorem exists_openExtensionAtClosedPoint
    {k : Type u} [Field k] (X Y : SchemeOverField k) [Curve X] [Variety Y] [IsProper Y.hom]
    (U : X.left.Opens) [Nonempty U] (f : Over.mk (U.ι ≫ X.hom) ⟶ Y)
    (x : X.left) (hx : x ∈ closedPoints X.left) :
    let F := X.left.presheaf
    ∀ [IsDiscreteValuationRing (F.stalk x)],
    ∃ (U' : X.left.Opens) (hUU' : U ≤ U') (_ : x ∈ U')
      (f' : Over.mk (U'.ι ≫ X.hom) ⟶ Y),
      (Over.homMk (X.left.homOfLE hUU') (X.left.homOfLE_ι_assoc hUU' X.hom) :
        Over.mk (U.ι ≫ X.hom) ⟶ Over.mk (U'.ι ≫ X.hom)) ≫ f' = f := sorry

end AlgebraicGeometry.Curve
