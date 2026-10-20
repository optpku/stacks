module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.Algebraicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace RestrictionOfScalars

universe u

/- Proposition 97.11.5: Let `S` be a scheme. Let `X ⟶ Z ⟶ B` be morphisms of
algebraic spaces over `S`. If `Z ⟶ B` is finite locally free then
`Res_{Z/B}(X)` is an algebraic space. -/
@[stacks 05YF]
#check (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.instIsAlgebraicSpace :
    ∀ {S : Scheme.{u}} {X Z B : AlgebraicSpace S} (f : X ⟶ Z) (g : Z ⟶ B)
      [FiniteLocallyFree g],
      IsAlgebraicSpace (AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars.smallFunctor f g))
