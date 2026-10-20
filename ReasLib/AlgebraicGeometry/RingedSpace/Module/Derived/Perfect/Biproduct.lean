module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Triangulated

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect

/-- A binary biproduct of perfect derived modules is perfect. -/
theorem biprod {X : RingedSpace.{u}} {E F : ModuleDerived X}
    (hE : ModuleDerived.IsPerfect E) (hF : ModuleDerived.IsPerfect F) :
    ModuleDerived.IsPerfect (E ⊞ F) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
