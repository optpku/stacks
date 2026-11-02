/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyUnramified.Composition

/-!
# Formally unramified morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme is formally unramified when its
transformation of functors of points is formally unramified. This property is
stable under composition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is formally unramified if it is formally
unramified as a transformation of functors of points. -/
class FormallyUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- The morphism is formally unramified as a transformation of functors. -/
  ofFunctor : Scheme.Over.FormallyUnramified f

/-- A morphism of algebraic spaces is formally unramified if and only if it is
formally unramified as a transformation of functors of points. -/
theorem formallyUnramified_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyUnramified f ↔ Scheme.Over.FormallyUnramified f :=
  ⟨fun hf ↦ hf.ofFunctor, fun hf ↦ ⟨hf⟩⟩

namespace FormallyUnramified

/-- A morphism of algebraic spaces that is formally unramified as a
transformation of functors of points is formally unramified. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Scheme.Over.FormallyUnramified f) : FormallyUnramified f :=
  ⟨hf⟩

/-- A formally unramified morphism of algebraic spaces is formally unramified as
a transformation of functors of points. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyUnramified f] : Scheme.Over.FormallyUnramified f :=
  FormallyUnramified.ofFunctor

/-- The identity morphism of an algebraic space is formally unramified. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FormallyUnramified (𝟙 X) := by
  refine ⟨⟨?_⟩⟩
  intro T T' _ _ i _ x₁ x₂ h
  exact congrArg Prod.snd h

/-- A formally unramified morphism of algebraic spaces yields a formally
unramified transformation of functors of points. -/
instance toSchemeOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyUnramified f] : Scheme.Over.FormallyUnramified f :=
  spec

/-- The composite of two formally unramified morphisms of algebraic spaces is
formally unramified. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallyUnramified f] [FormallyUnramified g] :
    FormallyUnramified (f ≫ g) := by
  refine ⟨⟨?_⟩⟩
  intro T T' _ _ i _ x₁ x₂ h
  have hT := congrArg Prod.fst h
  have hZ := congrArg Prod.snd h
  apply (spec (f := f)).injective_lift i
  refine Prod.ext hT ?_
  apply (spec (f := g)).injective_lift i
  refine Prod.ext ?_ hZ
  change Y.functorOfPoints.map i.op (f.app _ x₁) =
    Y.functorOfPoints.map i.op (f.app _ x₂)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  exact congrArg (f.app _) hT

/-- Formally unramified morphisms of algebraic spaces are stable under
composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallyUnramified S : MorphismProperty (AlgebraicSpace S)) :=
  ⟨fun f g hf hg ↦ @comp _ _ _ _ f g hf hg⟩

end FormallyUnramified

end AlgebraicGeometry.AlgebraicSpace
