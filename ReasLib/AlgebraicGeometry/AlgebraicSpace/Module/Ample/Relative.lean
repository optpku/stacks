/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.MkIffOfInductiveProp
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictToScheme

/-!
# Relatively ample modules on algebraic spaces

An invertible module on an algebraic space is relatively ample for a morphism when that
morphism is representable and every scheme base change is relatively ample in the sense of
schemes.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicSpace CategoryTheory Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An invertible module `L` on an algebraic space `X` is relatively ample for a
morphism `f : X ⟶ Y` if `f` is representable by schemes and, after every base
change along a morphism from a scheme, the restricted pullback is relatively
ample in the scheme sense. -/
@[mk_iff RelativelyAmple.iff]
class RelativelyAmple {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (L : X.Modules) : Prop where
  /-- The morphism `f` is representable by schemes. -/
  representable : yoneda.relativelyRepresentable f
  /-- After any cartesian scheme base change, the restricted pullback is relatively
  ample as a module on schemes. -/
  ofScheme {Z W : Over S} {g : ofOver Z ⟶ Y} {pX : ofOver W ⟶ X} {pZ : W ⟶ Z} :
    IsPullback pX (ofOverMap pZ) f g →
      AlgebraicGeometry.RelativelyAmple pZ.left
        ((Modules.restrictToScheme W).obj ((Modules.pullback pX).obj L))

/-- A scheme morphism that is relatively ample in the scheme sense is relatively
ample as a morphism of algebraic spaces. -/
instance RelativelyAmple.ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    (L : (ofOver U).Modules)
    [AlgebraicGeometry.RelativelyAmple h.left ((Modules.restrictToScheme U).obj L)] :
    RelativelyAmple (ofOverMap h) L :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
