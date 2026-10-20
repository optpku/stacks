module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.DirectImage
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

/- 66.26.0.1 (1): a morphism `f : X ⟶ Y` of algebraic spaces induces the pullback functor
`f^* : Mod(𝒪_Y) ⟶ Mod(𝒪_X)` of sheaves of modules on the associated small étale ringed topoi. -/
@[stacks 03LU] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pullback :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Y.Modules ⥤ X.Modules)

/- 66.26.0.1 (2): a morphism `f : X ⟶ Y` of algebraic spaces induces the pushforward functor
`f_* : Mod(𝒪_X) ⟶ Mod(𝒪_Y)` of sheaves of modules on the associated small étale ringed topoi. -/
@[stacks 03LU] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.pushforward :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → X.Modules ⥤ Y.Modules)
