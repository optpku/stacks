/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.Criteria

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/- The base-change predicate asserts invertibility of all geometric-point cohomology maps. -/
#check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.cohomologyBaseChangeHolds :
  ∀ {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
    (_ : IsPullback g' f' f g) (K : DerivedQCoh X) (K' : DerivedQCoh X')
    (_ : (ModuleDerived.pullback g').obj ((inclusion X).obj K) ⟶ (inclusion X').obj K'),
    Prop)

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
