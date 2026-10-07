module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Multiplication
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

/- 27.10.1.1: for `X = Proj(calA)`, multiplication on an integral twist family consists of
morphisms `P.twist n ⊗ P.twist m ⟶ P.twist (n + m)` for every `n m : Int`. -/
@[stacks 01MO] #check
  (AlgebraicGeometry.ProjTwistFamily.Multiplication :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] {calA : Nat -> sigma} [GradedRing calA]
      [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules],
      AlgebraicGeometry.ProjTwistFamily calA -> Type u)
