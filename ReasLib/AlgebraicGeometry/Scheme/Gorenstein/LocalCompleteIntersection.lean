/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocallyOfType
public import ReasLib.RingTheory.Gorenstein.CompleteIntersection

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme

/-- A locally complete-intersection morphism with Gorenstein target has Gorenstein source. -/
theorem gorenstein_of_isLocalCompleteIntersection
    {X Y : Scheme.{u}} (f : Y ⟶ X)
    [LocallyOfType RingHom.IsLocalCompleteIntersection f] [Gorenstein X] :
    Gorenstein Y := sorry

end AlgebraicGeometry.Scheme
