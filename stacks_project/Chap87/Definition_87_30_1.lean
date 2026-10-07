module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

/- Definition 87.30.1 (1): a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` is separated if the relative diagonal `diagonal f` is a closed
immersion. -/
@[stacks 0ARN] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.Separated :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)

/- Definition 87.30.1 (2): a morphism `f : X ⟶ Y` of formal algebraic spaces over a
scheme `S` is quasi-separated if the relative diagonal `diagonal f` is
quasi-compact. -/
@[stacks 0ARN] #check
  (AlgebraicGeometry.FormalAlgebraicSpace.QuasiSeparated :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)
