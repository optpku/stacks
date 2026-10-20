module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.LimitPreservingOnObjects
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects
open scoped Bicategory

universe u

/- 97.5.0.1: the commuting square p(x_{i'}|_U) ⟶ (y_i|_{U_{i'}})|_U over
p(x) ⟶ y_i|_U, with right vertical the canonical identification of iterated
restriction. -/
@[stacks 06CU] #check (AlgebraicGeometry.Groupoids.Hom.LimitPreservingOnObjects.commSq :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S} {p : X ⟶ Y} {I : Type u} [Preorder I]
    {D : OrderDual I ⥤ Over S} {c : Cone D} {i : I} {prob : Problem p D c i},
    Candidate prob → Prop)
