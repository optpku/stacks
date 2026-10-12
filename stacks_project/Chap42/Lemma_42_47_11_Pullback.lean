/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Definition_42_46_3_DerivedChern

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
