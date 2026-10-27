/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.DualNumber

/-! # Infinitesimal automorphisms and tangent spaces of scheme deformations -/

open CategoryTheory AlgebraicGeometry
universe u
variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X Y : Scheme.{u}) (f : X ⟶ Y)
variable (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
variable (hf : f ≫ hY = hX)

#check (FlatSchemeCat.inf Λ k X hX : Type u)
#check (FlatSchemeCat.tangentSpace Λ k X hX : Type (u + 1))
#check (FlatSchemeMorphismCat.inf Λ k f hX hY hf : Type u)
#check (FlatSchemeMorphismCat.tangentSpace Λ k f hX hY hf : Type (u + 1))
