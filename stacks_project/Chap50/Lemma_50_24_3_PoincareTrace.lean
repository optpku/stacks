/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Forms

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

#check (AlgebraicGeometry.Scheme.DeRham.pushforwardForm :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ),
    RingedSpace.ModuleDerived S.toRingedSpace)

end AlgebraicGeometry.Scheme.DeRham
