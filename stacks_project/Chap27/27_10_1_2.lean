module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Multiplication
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u v

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
  (AlgebraicGeometry.ProjTwistFamily.twist_def :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] {calA : Nat -> sigma} [GradedRing calA]
      (P : AlgebraicGeometry.ProjTwistFamily calA) (n : Int),
      P.twist n = P n)

#check
  (AlgebraicGeometry.ProjTwistFamily.tensorTwist :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] {calA : Nat -> sigma} [GradedRing calA]
      [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules],
      AlgebraicGeometry.ProjTwistFamily calA ->
        (AlgebraicGeometry.Proj calA).Modules -> Int ->
        (AlgebraicGeometry.Proj calA).Modules)

#check
  (AlgebraicGeometry.ProjTwistFamily.tensorTwist_def :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] {calA : Nat -> sigma} [GradedRing calA]
      [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules]
      (P : AlgebraicGeometry.ProjTwistFamily calA)
      (F : (AlgebraicGeometry.Proj calA).Modules) (n : Int),
      P.tensorTwist F n = tensorObj F (P.twist n))

#check
  (AlgebraicGeometry.ProjTwistFamily.Multiplication :
    forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] {calA : Nat -> sigma} [GradedRing calA]
      [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules]
      (P : AlgebraicGeometry.ProjTwistFamily calA),
      Type u)

#check (AlgebraicGeometry.projSheafTwistMul_def :
  forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
    [AddSubgroupClass sigma A]
    (calA : Nat -> sigma) [GradedRing calA]
    [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules]
    [BraidedCategory (AlgebraicGeometry.Proj calA).Modules]
    (twist : AlgebraicGeometry.ProjTwistFamily calA)
    (twistMul : AlgebraicGeometry.ProjTwistFamily.Multiplication twist)
    (F : (AlgebraicGeometry.Proj calA).Modules) (n m : Int),
    AlgebraicGeometry.projSheafTwistMul calA twist twistMul F n m =
      (α_ (twist n) F (twist m)).inv ≫
        ((β_ (twist n) F).hom ⊗ₘ 𝟙 (twist m)) ≫
        (α_ F (twist n) (twist m)).hom ≫
        (𝟙 F ⊗ₘ twistMul n m))

/- 27.10.1.2: for `X = Proj(calA)`, multiplication on an integral twist family induces
`O_X(n) ⊗ F(m) ⟶ F(n + m)`, where `F(m) = F ⊗ O_X(m)`. -/
@[stacks 03GJ]
#check (AlgebraicGeometry.projSheafTwistMul :
  forall {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
    [AddSubgroupClass sigma A]
    (calA : Nat -> sigma) [GradedRing calA]
    [MonoidalCategory (AlgebraicGeometry.Proj calA).Modules]
    [BraidedCategory (AlgebraicGeometry.Proj calA).Modules]
    (P : AlgebraicGeometry.ProjTwistFamily calA) (twistMul : P.Multiplication)
    (F : (AlgebraicGeometry.Proj calA).Modules) (n m : Int),
    (tensorObj (P.twist n) (P.tensorTwist F m) :
      (AlgebraicGeometry.Proj calA).Modules) ⟶
      P.tensorTwist F (n + m))
