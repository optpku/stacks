/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Algebraic spaces over Spec ℤ

The shared base-extension construction views an algebraic space over any
scheme as an algebraic space over `Spec ℤ`.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Compatibility access to the shared extension to the explicit terminal scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.toSpecZ :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    AlgebraicSpace (Spec (.of (ULift.{u} ℤ))))

end AlgebraicGeometry.AlgebraicSpace
