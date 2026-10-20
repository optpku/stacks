/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothFunctor

/-! Compatibility checks for smooth morphisms of set-valued functors. -/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (CategoryTheory.NatTrans.IsSmooth :
  ∀ {F G : ArtinianLocalAlgCat Λ k ⥤ Type v}, (F ⟶ G) → Prop)

#check (CategoryTheory.NatTrans.liftPair :
  ∀ {F G : ArtinianLocalAlgCat Λ k ⥤ Type v} (η : F ⟶ G)
    {B A : ArtinianLocalAlgCat Λ k} (f : B ⟶ A),
    F.obj B → F.obj A × G.obj B)
