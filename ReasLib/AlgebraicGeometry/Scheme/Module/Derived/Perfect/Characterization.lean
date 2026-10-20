module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- On a Noetherian scheme, a derived module is perfect if and only if all its
cohomology sheaves are coherent and it has finite Tor dimension. -/
@[stacks 03TP]
theorem isPerfect_iff_coherentCohomology_and_hasFiniteTorDimension
    {X : Scheme.{u}} [IsNoetherian X]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    (K : RingedSpace.ModuleDerived X.toRingedSpace) :
    RingedSpace.ModuleDerived.IsPerfect K ↔
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K ∧
        RingedSpace.HasFiniteTorDimension K := sorry

/-- Every cohomology sheaf of a perfect derived module on a Noetherian scheme
is coherent. -/
theorem IsPerfect.cohomologyIn_isCoherent
    {X : Scheme.{u}} [IsNoetherian X]
    {K : RingedSpace.ModuleDerived X.toRingedSpace}
    (hK : RingedSpace.ModuleDerived.IsPerfect K) :
    DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K := sorry

/-- A perfect derived module on a Noetherian scheme has finite Tor dimension. -/
theorem IsPerfect.hasFiniteTorDimension
    {X : Scheme.{u}} [IsNoetherian X]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    {K : RingedSpace.ModuleDerived X.toRingedSpace}
    (hK : RingedSpace.ModuleDerived.IsPerfect K) :
    RingedSpace.HasFiniteTorDimension K := sorry

/-- On a Noetherian scheme, a derived module with coherent cohomology in every
degree and finite Tor dimension is perfect. -/
theorem isPerfect_of_coherentCohomology_of_hasFiniteTorDimension
    {X : Scheme.{u}} [IsNoetherian X]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    {K : RingedSpace.ModuleDerived X.toRingedSpace}
    (hcoh : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K)
    (htor : RingedSpace.HasFiniteTorDimension K) :
    RingedSpace.ModuleDerived.IsPerfect K := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
