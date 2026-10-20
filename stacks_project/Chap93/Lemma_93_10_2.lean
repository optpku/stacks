/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.RimSchlessinger
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for morphisms of schemes

Example 93.10.1 satisfies (RS), so `Def_{X ⟶ Y}` is a deformation category for
any morphism of schemes `X ⟶ Y` over `k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (X Y : Scheme.{u}) (f : X ⟶ Y)
  (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
  (hf : f ≫ hY = hX)

/- Lemma 93.10.2 (1)
Example 93.10.1 satisfies the Rim-Schlessinger condition (RS). -/
@[stacks 0E3U]
#check (FlatSchemeMorphismCat.instHasRimSchlessinger_forget Λ k :
  HasRimSchlessinger (FlatSchemeMorphismCat.forget Λ k))

/- Lemma 93.10.2 (2)
In particular, `Def_{X ⟶ Y}` is a deformation category for any morphism of
schemes `X ⟶ Y` over `k`. -/
@[stacks 0E3U]
#check (FlatSchemeMorphismCat.instIsDeformationCategory_deformationForget Λ k X Y f hX hY hf :
  IsDeformationCategory (FlatSchemeMorphismCat.deformationForget Λ k X Y f hX hY hf))
