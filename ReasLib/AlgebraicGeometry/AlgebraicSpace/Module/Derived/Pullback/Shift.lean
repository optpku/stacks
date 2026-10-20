module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.CategoryTheory.Functor.Derived.Total.Triangulated

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- Module pullback is pointwise left derivable at every homotopy complex. -/
instance hasPointwiseLeftDerivedFunctorAt_pullback
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (K : HomotopyCategory Y.Modules (up ℤ)) :
    (Functor.Homotopy.toDerived (Modules.pullback f)).HasPointwiseLeftDerivedFunctorAt
      (HomotopyCategory.quasiIso Y.Modules (up ℤ)) K :=
  sorry

/-- Concrete derived pullback commutes with integer shifts through its canonical
comparison with total left derived pullback. -/
noncomputable instance pullback.commShift
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    (pullback f).CommShift ℤ :=
  Functor.CommShift.ofIso (pullbackIsoTotalLeftDerived f).symm ℤ

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
