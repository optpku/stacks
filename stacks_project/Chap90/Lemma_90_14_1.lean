/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SubringOver.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open Functor
open Functor.SubringOver

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

/- Lemma 90.14.1. Pushforward preserves minimal objects and, over a surjective
base map, reaches every minimal object up to isomorphism. -/
@[stacks 06T1] #check (CategoryTheory.Functor.SubringOver.pushforward_preserves_isMinimal :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] {x y : F} (φ : y ⟶ x)
    {a : SubringOver p y} (ha : IsMinimal a),
    IsMinimal ((pushforward p φ).obj a))

#check (CategoryTheory.Functor.SubringOver.exists_isMinimal_of_surjective :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p] {x y : F} (φ : y ⟶ x)
    (hφ : Function.Surjective (p.map φ).hom) (a : SubringOver p x) (ha : IsMinimal a),
    ∃ b : SubringOver p y, IsMinimal b ∧ Nonempty ((pushforward p φ).obj b ≅ a))
