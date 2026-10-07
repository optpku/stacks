module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.SectionComponent.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Shrinking for fibre components selected by a section
-/

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.Section

/-- For a finite-type morphism with a section and a point `y`, there is a
nonempty open of the reduced closure of `y` over which the inverse image of the
section-selected component locus is open and closed. -/
theorem exists_open_pointClosure_componentLocus_isClopen
    {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X)
    (hs : s ≫ f = 𝟙 Y) [FiniteType f] (y : Y) :
    ∃ V : (PointClosure.scheme y).Opens, Nonempty V ∧
      IsClopen
        ((pullback.fst f (V.ι ≫ PointClosure.ι y)) ⁻¹'
          componentLocus f s hs) := sorry

end AlgebraicGeometry.Scheme.Hom.Section
