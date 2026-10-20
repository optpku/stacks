/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Picard.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Invertible.Properties
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper.BaseChange

/-! # The natural inclusion of invertible modules into coherent families -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Picard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- An invertible module on a fiber defines a finitely presented relatively flat
module with proper support when the structure morphism is flat and proper. -/
def toCohObj (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    (x : Obj f) : CohStack.Obj f where
  σ := x.σ
  module := x.line
  isFinitePresentation := Modules.isFinitePresentationOfIsInvertible x.line x.invertible
  isFlat := Modules.flatOverOfIsInvertible x.line (CohStack.fiberToBase f x.σ)
    x.invertible (flat_pullback_snd f x.σ.hom)
  hasProperSupport := Modules.instHasProperSupportOver_of_proper
    (Limits.pullback.snd f x.σ.hom) x.line

/-- A Picard morphism defines the coherent-family morphism with the same base
map and module isomorphism. -/
def toCohMap (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    {x y : Obj f} (α : x ⟶ y) : toCohObj f x ⟶ toCohObj f y :=
  CohStack.homMk α.base α.iso

/-- The inclusion of Picard morphisms preserves identities. -/
theorem toCohMapId (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    (x : Obj f) : toCohMap f (𝟙 x) = 𝟙 (toCohObj f x) := sorry

/-- The inclusion of Picard morphisms preserves composition. -/
theorem toCohMapComp (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    {x y z : Obj f} (α : x ⟶ y) (β : y ⟶ z) :
    toCohMap f (α ≫ β) = toCohMap f α ≫ toCohMap f β := sorry

/-- The identity-on-triples functor from invertible modules to finitely presented
relatively flat modules with proper support. -/
def toCoh (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    Obj f ⥤ CohStack.Obj f where
  obj := toCohObj f
  map := toCohMap f
  map_id := toCohMapId f
  map_comp := fun α β ↦ toCohMapComp f α β

/-- `toCoh` preserves the underlying test scheme. -/
theorem toCoh_obj_σ (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    (x : Obj f) : ((toCoh f).obj x).σ = x.σ := sorry

/-- `toCoh` preserves the underlying module on the fibre. -/
theorem toCoh_obj_module (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    (x : Obj f) : ((toCoh f).obj x).module = x.line := sorry

/-- The inclusion preserves both the test scheme and the module on its fiber. -/
theorem toCoh_obj_spec (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f]
    (x : Obj f) : ((toCoh f).obj x).σ = x.σ ∧
      ((toCoh f).obj x).module = x.line := sorry

/-- The identity-on-triples functor lies strictly over `Over S`. -/
theorem toCoh_p (f : X ⟶ B) [Flat f] [FinitePresentation f] [Proper f] :
    toCoh f ⋙ CohStack.p f = p f := sorry

end AlgebraicGeometry.AlgebraicSpace.Picard
