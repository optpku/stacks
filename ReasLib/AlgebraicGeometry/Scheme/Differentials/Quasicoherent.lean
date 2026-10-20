/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Affine

/-!
# Quasi-coherent relative differentials

The relative differential sheaf of a morphism of schemes is quasi-coherent.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The relative differential sheaf of a morphism of schemes is quasi-coherent. -/
instance isQuasicoherent_differentials (f : X ⟶ S) :
    (Ω[f.toShHom]).IsQuasicoherent := sorry

end AlgebraicGeometry
