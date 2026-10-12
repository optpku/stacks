/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.SchemeOverField
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- The degree-`0` derived object associated to a coherent `𝒪_X`-module on a regular scheme,
as an object of `PerfectDerived X`. -/
def ofCoherentZeroDimSupport {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : Coh X.left.toRingedSpace) : PerfectDerived X :=
  { obj := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ.obj
    property := sorry }

/-- On a regular scheme, the inclusion of `ofCoherentZeroDimSupport X ℱ` recovers the
degree-`0` derived object of the coherent module `ℱ`. -/
theorem ofCoherentZeroDimSupport_obj {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : Coh X.left.toRingedSpace) :
    (inclusion X).obj (ofCoherentZeroDimSupport X ℱ) =
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ.obj := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
