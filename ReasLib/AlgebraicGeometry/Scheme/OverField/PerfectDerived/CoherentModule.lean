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
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.PerfectDerived

/-- The degree-`0` derived object associated to a coherent `𝒪_X`-module, as an object of
`PerfectDerived X`. -/
def ofCoherentModule {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ] :
    PerfectDerived X :=
  { obj := (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ
    property := sorry }

/-- The inclusion of the degree-`0` derived object associated to a coherent module. -/
theorem ofCoherentModule_obj {k : Type u} [Field k] (X : SchemeOverField k)
    [Scheme.Regular X.left] (ℱ : X.left.Modules) [SheafOfModules.IsCoherent ℱ] :
    (inclusion X).obj (ofCoherentModule X ℱ) =
      (DerivedCategory.singleFunctor X.left.Modules (0 : ℤ)).obj ℱ := sorry

end AlgebraicGeometry.SchemeOverField.PerfectDerived

end
