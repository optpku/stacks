/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.DualNumber
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Finite-dimensional deformation spaces of morphisms between proper schemes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace FlatSchemeMorphismCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
variable (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
variable (hf : f ≫ hY = hX)

/-- The infinitesimal automorphism space of a morphism between proper schemes over a field
is finite-dimensional over that field. -/
instance instFiniteDimensional_inf [IsProper hX] [IsProper hY] :
    FiniteDimensional k (inf Λ k f hX hY hf) := sorry

/-- The tangent space of the deformation category of a morphism between proper schemes
over a field is finite-dimensional over that field. -/
instance instFiniteDimensional_tangentSpace [IsProper hX] [IsProper hY] :
    FiniteDimensional k (tangentSpace Λ k f hX hY hf) := sorry

end FlatSchemeMorphismCat
