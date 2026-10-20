module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 72.8.1: Let `S` be a scheme. Let `X` be an integral algebraic space
over `S`. A modification of `X` is a birational proper morphism `f : X' ⟶ X` of
algebraic spaces over `S` with `X'` integral. -/
@[stacks 0AD8] #check (AlgebraicGeometry.AlgebraicSpace.IsModification :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X], (X' ⟶ X) → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.isModification_iff :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X),
    IsModification f ↔ IsBirational f ∧ Proper f)
