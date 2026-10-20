module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.Pullback

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Derived.IsDefined

#check (AlgebraicGeometry.ChernClass.Derived.IsDefined.pullback :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y)
    {E : RingedSpace.ModuleDerived Y.toRingedSpace} (defined : IsDefined E),
    IsDefined ((RingedSpace.modulePullbackDerived f.toShHom).obj E))

end AlgebraicGeometry.ChernClass.Derived.IsDefined
