/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.DualObstruction

@[expose] public section

open CategoryTheory AlgebraicGeometry
noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} [IsLocallyNoetherian S]

/-- The fibre object associated to an object over an affine spectrum. -/
def toFiber {X : GroupoidsOver S} (ξ : ObjectOverSpec X) :
    X.p.Fiber (Over.mk ξ.toS) :=
  Spectrum.ObjectOverSpec.toFiber ξ

end AlgebraicGeometry.GroupoidsOver

#check (AlgebraicGeometry.GroupoidsOver.toFiber :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    (ξ : AlgebraicGeometry.GroupoidsOver.ObjectOverSpec X),
    X.p.Fiber (Over.mk ξ.toS))

#check (AlgebraicGeometry.GroupoidsOver.DualObstruction :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S] (X : GroupoidsOver S)
    [AlgebraicGeometry.GroupoidsOver.HasStrongRimSchlessinger X], Type (u + 1))
