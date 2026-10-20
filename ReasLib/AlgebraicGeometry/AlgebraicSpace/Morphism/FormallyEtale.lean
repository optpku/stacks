/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.Scheme.Over.FormallyLifting

/-!
# Formally étale morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is formally étale when it is
formally étale as a transformation of functors of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces is formally étale if it is formally étale as
a transformation of functors of points. -/
class FormallyEtale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- The morphism is formally étale as a transformation of functors. -/
  ofFunctor : Scheme.Over.FormallyEtale f

/-- A morphism of algebraic spaces is formally étale if and only if it is
formally étale as a transformation of functors of points. -/
theorem formallyEtale_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyEtale f ↔ Scheme.Over.FormallyEtale f :=
  sorry

namespace FormallyEtale

/-- A morphism of algebraic spaces that is formally étale as a transformation
of functors of points is formally étale. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : Scheme.Over.FormallyEtale f) : FormallyEtale f :=
  sorry

/-- A formally étale morphism of algebraic spaces is formally étale as a
transformation of functors of points. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyEtale f] : Scheme.Over.FormallyEtale f :=
  sorry

/-- The identity morphism of an algebraic space is formally étale. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    FormallyEtale (𝟙 X) :=
  sorry

/-- A formally étale morphism of algebraic spaces yields a formally étale
transformation of functors of points. -/
instance toSchemeOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyEtale f] : Scheme.Over.FormallyEtale f :=
  sorry

/-- The composite of formally étale morphisms of algebraic spaces is formally
étale. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallyEtale f] [FormallyEtale g] :
    FormallyEtale (f ≫ g) :=
  sorry

/-- Formally étale morphisms of algebraic spaces are stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@FormallyEtale S : MorphismProperty (AlgebraicSpace S)) :=
  sorry

/-- Formally étale morphisms of algebraic spaces are stable under
arbitrary base change. -/
instance instIsStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange
      (@FormallyEtale S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The base-change projection `pullback.snd f g` of a formally étale
morphism `f : X ⟶ Y` is formally étale. -/
instance pullback_snd {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Z ⟶ Y) [HasPullback f g] [FormallyEtale f] :
    FormallyEtale (pullback.snd f g) := sorry

end FormallyEtale

end AlgebraicGeometry.AlgebraicSpace
