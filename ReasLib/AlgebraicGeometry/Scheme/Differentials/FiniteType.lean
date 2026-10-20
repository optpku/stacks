/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Affine
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Finite type relative differentials

The relative differential sheaf of a locally finite type morphism of schemes is finite type.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The relative differential sheaf of a locally finite type morphism of schemes is a finite-type
module sheaf. -/
instance isFiniteType_differentials_of_locallyOfFiniteType
    (f : X ⟶ S) [LocallyOfFiniteType f] :
    (Ω[f.toShHom]).IsFiniteType := sorry

end AlgebraicGeometry
