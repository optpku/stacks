module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Lifting
import StacksCheckRecall

open CategoryTheory

universe u

/- Definition 37.6.1: a scheme morphism is formally unramified when lifts through every affine
first-order thickening over the base are unique whenever they exist. -/
@[stacks 02H8] #check
  (AlgebraicGeometry.FormallyUnramified.iff_subsingleton_liftStruct_of_affine :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      AlgebraicGeometry.FormallyUnramified f ↔
        ∀ {T T' : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine T]
          [AlgebraicGeometry.IsAffine T'] (i : T ⟶ T') [AlgebraicGeometry.IsClosedImmersion i]
          (h_square : i.ker ^ 2 = 0) (g : T ⟶ X) (h : T' ⟶ S)
          (sq : CommSq g i f h), Subsingleton sq.LiftStruct)

/- Formal unramifiedness gives uniqueness of lifts through nilpotent closed immersions. -/
#check @AlgebraicGeometry.FormallyUnramified.hom_ext

/- Conversely, uniqueness of lifts through affine square-zero thickenings implies formal
unramifiedness. -/
#check @AlgebraicGeometry.FormallyUnramified.of_hom_ext
