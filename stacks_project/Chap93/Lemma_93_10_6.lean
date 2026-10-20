/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SchemeMorphism.SourceEquivalence
import StacksCheckRecall

/-!
# Source equivalence of morphism deformation categories

If `f : X ⟶ Y` is a morphism of schemes over `k` with `f_* 𝒪_X = 𝒪_Y` and
`R¹ f_* 𝒪_X = 0`, then the forgetful morphism of deformation categories
`Def_{X ⟶ Y} ⥤ᵇ Def_X` is an equivalence.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped BasedFunctor

universe u

/- Lemma 93.10.6
In Example 93.9.1 let `f : X ⟶ Y` be a morphism of schemes over `k`. If
`f_* 𝒪_X = 𝒪_Y` and `R¹ f_* 𝒪_X = 0`, then the morphism of deformation
categories `FlatSchemeMorphismCat.sourceBasedFunctor Λ k X Y f hX hY hf` is an equivalence. -/
@[stacks 0E3X] #check (FlatSchemeMorphismCat.instIsEquivalence_sourceBasedFunctor :
  ∀ (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [h_pushforward : IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom)]
    [h_R1 : Fact
      (IsZero
        (RingedSpace.Hom.higherDirectImageModule f.toShHom
          (SheafOfModules.unit X.ringCatSheaf) 1))],
    BasedFunctor.IsEquivalence
      (FlatSchemeMorphismCat.sourceBasedFunctor Λ k X Y f hX hY hf))
