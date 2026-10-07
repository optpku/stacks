module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.RLinearModel
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.OverField.PerfectDerived
public import Mathlib.CategoryTheory.Linear.Yoneda

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/- The compatibility view of the restricted representable functor is the promoted
   `AlgebraicGeometry.SchemeOverField.PerfectDerived.representedBy`. -/
#check
  (AlgebraicGeometry.SchemeOverField.PerfectDerived.representedBy :
    {k : Type u} → [Field k] → (X : SchemeOverField k) →
      (K : RingedSpace.ModuleDerived X.left.toRingedSpace) →
        (PerfectDerived X)ᵒᵖ ⥤ ModuleCat k)

end AlgebraicGeometry.SchemeOverField

end
