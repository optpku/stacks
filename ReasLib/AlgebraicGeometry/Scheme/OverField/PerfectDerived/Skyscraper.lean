/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Local
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace.Module

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- The degree-zero residue-field skyscraper at a closed point of a proper regular scheme
over a field is perfect. -/
theorem isPerfect_residueFieldSkyscraper {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left) :
    RingedSpace.ModuleDerived.IsPerfect
      ((DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj
        (Skyscraper.atPoint x
          (ModuleCat.of (RingCat.of (stalkRing X x))
            (IsLocalRing.ResidueField (stalkRing X x))))) := sorry

/-- The residue-field skyscraper at a closed point of a proper regular scheme over a field,
viewed as a perfect derived object concentrated in degree zero. -/
def residueFieldSkyscraper {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left) : PerfectDerived X :=
  { obj :=
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj
        (Skyscraper.atPoint x
          (ModuleCat.of (RingCat.of (stalkRing X x))
            (IsLocalRing.ResidueField (stalkRing X x))))
    property := isPerfect_residueFieldSkyscraper X x hx }

/-- The inclusion of the perfect residue-field skyscraper recovers the degree-zero derived
skyscraper with value the residue field of the stalk ring. -/
theorem residueFieldSkyscraper_obj {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] [Scheme.Regular X.left]
    (x : X.left) (hx : x ∈ closedPoints X.left) :
    (inclusion X).obj (residueFieldSkyscraper X x hx) =
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj
        (Skyscraper.atPoint x
          (ModuleCat.of (RingCat.of (stalkRing X x))
            (IsLocalRing.ResidueField (stalkRing X x)))) := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
