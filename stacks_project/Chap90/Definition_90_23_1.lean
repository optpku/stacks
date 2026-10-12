/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.SmoothGroupoid
import StacksCheckRecall

/-! Smooth groupoids in functors on the base category. -/

@[expose] public section

open CategoryTheory

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Definition 90.23.1: a groupoid in functors is smooth when its source and target
maps are smooth; the composition map does not enter this predicate. -/
@[stacks 06KI] #check (CategoryTheory.GroupoidInFunctors.IsSmooth :
  ∀ {U R : ArtinianLocalAlgCat Λ k ⥤ Type v}, (R ⟶ U) → (R ⟶ U) → Prop)
