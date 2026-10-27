/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Automorphism

/-! # Automorphism functors of families of curves

Typed compatibility checks for the automorphism-presheaf API.
-/

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.asFiber :
  ∀ {S : Scheme.{u}} (P : Obj S), (p S).Fiber (base P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.autFunctor :
  ∀ {S : Scheme.{u}} (P : Obj S), (Over (base P).left)ᵒᵖ ⥤ Type (u + 1))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.autFunctor_isRepresentable :
  ∀ {S : Scheme.{u}} (P : Obj S),
    ∃ G : AlgebraicSpace (base P).left, IsRepresentedBy P G)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
