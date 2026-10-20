/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj

/-!
# Properness of blowups of algebraic spaces

The blowup morphism in a finite-type quasi-coherent ideal sheaf is proper.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The structure morphism of a blowup of an algebraic space in a finite-type
quasi-coherent ideal sheaf is proper. -/
theorem proper_of_isFiniteType {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] [I.toModule.IsFiniteType]
    (π : Blowup X I) : Proper π.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
