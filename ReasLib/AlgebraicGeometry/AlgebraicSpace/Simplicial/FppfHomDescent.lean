/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.HomSequence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Simplicial.FppfHypercovering
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.CategoryTheory.ComposableArrows.Three
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace CategoryTheory.ComposableArrows Functor
open scoped DerivedExt Simplicial ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Simplicial

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable {U : SimplicialObject (AlgebraicSpace S)}
variable (a : U ⟶ (const SimplexCategoryᵒᵖ).obj X)

/-- Negative Ext groups of two quasi-coherent derived module objects vanish
if they vanish after pullback to every stage of an fppf hypercovering. -/
@[stacks 0DL9]
theorem negExtSubsingleton (ha : IsFppfHypercovering a)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (h_ext : ∀ n : ℕ, ∀ i : ℤ, i < 0 →
      Subsingleton
        (Ext⁽i⁾((modulePullbackDerived (a.app (op ⦋n⦌))).obj K.obj,
          (modulePullbackDerived (a.app (op ⦋n⦌))).obj E.obj)))
    (i : ℤ) (hi : i < 0) :
    Subsingleton (Ext⁽i⁾(K.obj, E.obj)) := sorry

/-- The degree-zero and degree-one Čech Hom sequence of two quasi-coherent
derived module objects is exact when their stagewise negative Ext groups
vanish on an fppf hypercovering. -/
@[stacks 0DL9]
theorem homSequence_exact (ha : IsFppfHypercovering a)
    (K E : AlgebraicSpace.DerivedQCoh X)
    (h_ext : ∀ n : ℕ, ∀ i : ℤ, i < 0 →
      Subsingleton
        (Ext⁽i⁾((modulePullbackDerived (a.app (op ⦋n⦌))).obj K.obj,
          (modulePullbackDerived (a.app (op ⦋n⦌))).obj E.obj))) :
    (mk₃ (0 : 0 ⟶ AddCommGrpCat.of (K.obj ⟶ E.obj))
      (homRestrict a K E) (homDiff a K E)).Exact := sorry

end AlgebraicGeometry.AlgebraicSpace.Simplicial

end
