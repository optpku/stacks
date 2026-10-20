module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Resolution
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

/- Definition 89.8.1: Let `S` be a scheme. Let `Y` be a Noetherian integral algebraic space
over `S`. A resolution of singularities of `Y` is a modification `f : X ⟶ Y` such that
`X` is regular. -/
@[stacks 0BHW] #check (AlgebraicGeometry.AlgebraicSpace.IsResolution :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X], (X ⟶ Y) → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.isResolution_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsNoetherian Y] [IsIntegral Y] [IsIntegral X] (f : X ⟶ Y),
    IsResolution f ↔ IsModification f ∧ IsRegular X)
