module

public import ReasLib.AlgebraicGeometry.Scheme.Compactification.Category
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Localization.CalculusOfFractions

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- For a quasi-compact quasi-separated scheme `S`, compactification morphisms whose interior
component is an isomorphism have a right calculus of fractions. -/
instance hasRightCalculusOfFractions (S : Scheme.{u}) [CompactSpace S]
    [QuasiSeparatedSpace S] : (interiorIsomorphisms S).HasRightCalculusOfFractions := sorry

end AlgebraicGeometry.Scheme.Compactification
