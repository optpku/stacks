module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.Conormal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocalCompleteIntersection.Finiteness
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified.Differentials
import StacksCheckRecall

/-!
# Unramified local complete intersection morphisms of algebraic spaces

A local complete intersection morphism of algebraic spaces is unramified if and
only if it is formally unramified, and in that case the conormal sheaf of any
universal first-order thickening is finite locally free.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

section

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocalCompleteIntersection f]

/- Lemma 76.48.12 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a local
complete intersection morphism of algebraic spaces over `S`. Then `f` is
unramified if and only if `f` is formally unramified. -/
@[stacks 06CB] #check
  (AlgebraicGeometry.AlgebraicSpace.Unramified.iff_formallyUnramified :
    Unramified f ↔ FormallyUnramified f)

end

/- Lemma 76.48.12 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a formally
unramified local complete intersection morphism of algebraic spaces over `S`.
Then the conormal sheaf `Hom.conormalSheaf i` of any universal first-order
thickening `i` of `X` over `Y` is finite locally free on `X`. The relative
conormal sheaf of the composite `i ≫ f` is represented by this sheaf for every
universal first-order thickening `i` over `Y`. -/
@[stacks 06CB] #check
  (AlgebraicGeometry.AlgebraicSpace.IsUniversalFirstOrder.conormalSheaf_isFiniteLocallyFree :
    ∀ {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} (i : X ⟶ X') (f : X' ⟶ Y)
      [FormallyUnramified (i ≫ f)] [IsLocalCompleteIntersection (i ≫ f)]
      [IsUniversalFirstOrder i f], (Hom.conormalSheaf i).IsFiniteLocallyFree)

end AlgebraicGeometry.AlgebraicSpace
