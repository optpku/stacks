module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

variable {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
  {calA : Nat -> sigma} [GradedRing calA]

#check
  (AlgebraicGeometry.ProjTwistFamily :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] (calA : Nat -> sigma) [GradedRing calA],
      Type (u + 1))

#check
  (AlgebraicGeometry.ProjTwistFamily.twist :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] {calA : Nat -> sigma} [GradedRing calA],
      AlgebraicGeometry.ProjTwistFamily calA -> Int ->
        (AlgebraicGeometry.Proj calA).Modules)

#check
  (AlgebraicGeometry.ProjTwistFamily.tensorTwist :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] {calA : Nat -> sigma} [GradedRing calA]
      [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules],
      AlgebraicGeometry.ProjTwistFamily calA ->
        (AlgebraicGeometry.Proj calA).Modules -> Int ->
        (AlgebraicGeometry.Proj calA).Modules)

/- Definition 27.10.1: Let `X = Proj(S)`. The sheaf `O_X(n)` is the module sheaf
associated to the grading shift `S(n)`, and the twist of a module sheaf `F` is
`F(n) = F tensor O_X(n)`. Here `P` is the explicitly supplied family of these associated
module sheaves. -/
@[stacks 01MN] #check
  (AlgebraicGeometry.ProjTwistFamily.tensorTwist_def :
    forall [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules]
      (P : AlgebraicGeometry.ProjTwistFamily calA)
      (F : (AlgebraicGeometry.Proj calA).Modules) (n : Int),
      AlgebraicGeometry.ProjTwistFamily.tensorTwist P F n =
        tensorObj F (AlgebraicGeometry.ProjTwistFamily.twist P n))

#check
  (AlgebraicGeometry.ProjTwistFamily.twist_def :
    forall (P : AlgebraicGeometry.ProjTwistFamily calA) (n : Int),
      AlgebraicGeometry.ProjTwistFamily.twist P n = P n)
