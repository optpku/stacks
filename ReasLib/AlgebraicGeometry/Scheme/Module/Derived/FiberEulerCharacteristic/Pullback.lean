/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberBetti
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- Formation of the derived-fiber Euler-characteristic function of a pseudo-coherent
derived module commutes with arbitrary scheme base change. -/
theorem fiberEulerChar_pullback {X Y : Scheme.{u}} (f : Y ⟶ X)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPseudoCoherent E) :
    fiberEulerChar ((RingedSpace.modulePullbackDerived f.toShHom).obj E) =
      fun y : Y ↦ fiberEulerChar E (f y) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
