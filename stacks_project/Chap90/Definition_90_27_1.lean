/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Groupoid.Minimality
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

variable (G : GroupoidInFunctors.{u + 1, u, u} (ArtinianLocalAlgCat Λ k))
  [CategoryTheory.GroupoidInFunctors.IsSmooth G.s G.t]
  [CategoryTheory.GroupoidInFunctors.IsProrepresentable G]

/- Definition 90.27.1: a smooth prorepresentable groupoid is normalized if its
 dual-number fibre has no arrows between distinct objects, and minimal if its
 actual quotient presentation is given by a minimal versal formal object. -/
@[stacks 06KM] #check (CategoryTheory.GroupoidInFunctors.IsNormalized G : Prop)
#check (CategoryTheory.GroupoidInFunctors.IsNormalized.iff_totallyDisconnected G :
  CategoryTheory.GroupoidInFunctors.IsNormalized G ↔
    ∀ (x y : G.U.obj (ArtinianLocalAlgCat.dualNumber Λ k)),
      x ≠ y → IsEmpty (G.PointHom (ArtinianLocalAlgCat.dualNumber Λ k) x y))
#check (CategoryTheory.GroupoidInFunctors.IsMinimal G : Prop)
#check (CategoryTheory.GroupoidInFunctors.isMinimal_iff G :
  CategoryTheory.GroupoidInFunctors.IsMinimal G ↔
    ∃ (R : CompleteLocalAlgCat Λ k) (e : G.U ≅ CompleteLocalAlgCat.restrictedCoyoneda R),
      FormalObject.IsMinimalVersal (G.quotientFormalObject e))
