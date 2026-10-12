/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.FiniteLocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Radicial

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace DescentData
namespace IsEffective

/-- Every descent datum along a surjective finite locally free radicial morphism of schemes
is effective. -/
theorem ofFiniteLocallyFreeRadicial {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [IsFiniteLocallyFree f] [Radicial f]
    (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)) :
    D.IsEffective := sorry

end IsEffective
end DescentData
end Scheme
end AlgebraicGeometry
