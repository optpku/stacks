/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Biproduct
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent
public import ReasLib.AlgebraicGeometry.BivariantClass.Additive

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived.IsDefined

/-- Chern classes are defined for a binary biproduct when they are defined for both summands. -/
theorem biprod {X : Scheme.{u}} {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (hE : IsDefined E) (hF : IsDefined F) :
    IsDefined (E ⊞ F) := sorry

end AlgebraicGeometry.ChernClass.Derived.IsDefined

namespace AlgebraicGeometry.ChernClass.Derived

/-- Newton classes of perfect derived modules are additive under binary biproducts. -/
theorem newtonClass_biprod
    {S X : Scheme.{u}} [UniversallyCatenary S]
    (delta : S → ℤ) [IsDimensionFunction delta]
    (pi : X ⟶ S) [LocallyOfFiniteType pi] (classes : Theory delta pi)
    {E F : RingedSpace.ModuleDerived X.toRingedSpace}
    (perfectE : RingedSpace.ModuleDerived.IsPerfect E)
    (perfectF : RingedSpace.ModuleDerived.IsPerfect F)
    (definedE : IsDefined E) (definedF : IsDefined F) (p : ℕ) :
    newtonClass delta pi classes (E ⊞ F) (perfectE.biprod perfectF)
        (definedE.biprod definedF) p =
      BivariantClass.pointwiseAdd delta (𝟙 (Over.mk pi)) (p : ℤ)
        (newtonClass delta pi classes E perfectE definedE p)
        (newtonClass delta pi classes F perfectF definedF p) := sorry

end AlgebraicGeometry.ChernClass.Derived
