module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Derived.EnvelopeDescent

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry
namespace ChernClass
namespace Derived
namespace IsDefined

/-- Definedness of derived Chern classes is preserved by derived pullback. -/
theorem pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    {E : RingedSpace.ModuleDerived Y.toRingedSpace} (defined : IsDefined E) :
    IsDefined ((RingedSpace.modulePullbackDerived f.toShHom).obj E) := sorry

end IsDefined
end Derived
end ChernClass
end AlgebraicGeometry
