/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GlobalSections

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

universe u v

#check (@AlgebraicGeometry.ProjTwistGlobalSections.degree :
  ∀ {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] (calA : Nat → sigma) [GradedRing calA]
      (P : AlgebraicGeometry.ProjTwistFamily calA) (n : Nat), Type u)

#check (@AlgebraicGeometry.ProjTwistGlobalSections.twistedDegree :
  ∀ {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] (calA : Nat → sigma) [GradedRing calA]
      (P : AlgebraicGeometry.ProjTwistFamily calA)
      (F : (AlgebraicGeometry.Proj calA).Modules) (m : Int), Type u)

#check (@AlgebraicGeometry.ProjTwistGlobalSections.homogeneousAction :
  ∀ {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] (calA : Nat → sigma) [GradedRing calA]
      (P : AlgebraicGeometry.ProjTwistFamily calA) (mul : P.Multiplication)
      (F : (AlgebraicGeometry.Proj calA).Modules) (n : Nat) (m : Int),
    AlgebraicGeometry.ProjTwistGlobalSections.degree calA P n →+
      AlgebraicGeometry.ProjTwistGlobalSections.twistedDegree calA P F m →+
        AlgebraicGeometry.ProjTwistGlobalSections.twistedDegree calA P F ((n : Int) + m))

#check (@AlgebraicGeometry.ProjTwistGlobalSections.directSumActionHom :
  ∀ {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] (calA : Nat → sigma) [GradedRing calA]
      (P : AlgebraicGeometry.ProjTwistFamily calA) (mul : P.Multiplication)
      (F : (AlgebraicGeometry.Proj calA).Modules),
    (⨁ n : Nat, AlgebraicGeometry.ProjTwistGlobalSections.degree calA P n) →+
      ((⨁ m : Int,
          AlgebraicGeometry.ProjTwistGlobalSections.twistedDegree calA P F m) →+
        (⨁ m : Int,
          AlgebraicGeometry.ProjTwistGlobalSections.twistedDegree calA P F m)))

/- 27.10.1.4: for `X = Proj(𝒜)`, multiplication of the chosen twists induces the displayed map
`(⨁ n : ℕ, Γ(X, 𝒪_X(n))) × (⨁ m : ℤ, Γ(X, F(m))) ⟶ ⨁ m : ℤ, Γ(X, F(m))`. -/
@[stacks 03GK]
#check (@AlgebraicGeometry.ProjTwistGlobalSections.directSumAction :
  ∀ {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] (calA : Nat -> sigma) [GradedRing calA]
      (P : AlgebraicGeometry.ProjTwistFamily calA) (mul : P.Multiplication)
      (F : (AlgebraicGeometry.Proj calA).Modules),
    ((⨁ n : Nat, Γ(P.twist (n : Int), ⊤)) ×
      (⨁ m : Int, Γ(P.tensorTwist F m, ⊤))) →
        (⨁ m : Int, Γ(P.tensorTwist F m, ⊤)))

#check (@AlgebraicGeometry.ProjTwistGlobalSections.directSumAction_of_of :
  ∀ {A : Type u} {sigma : Type v} [CommRing A] [SetLike sigma A]
      [AddSubgroupClass sigma A] (calA : Nat -> sigma) [GradedRing calA]
      (P : AlgebraicGeometry.ProjTwistFamily calA) (mul : P.Multiplication)
      (F : (AlgebraicGeometry.Proj calA).Modules) (n : Nat) (m : Int)
      (x : Γ(P.twist (n : Int), ⊤)) (y : Γ(P.tensorTwist F m, ⊤)),
    AlgebraicGeometry.ProjTwistGlobalSections.directSumAction calA P mul F
        (DirectSum.of (fun i : Nat => Γ(P.twist (i : Int), ⊤)) n x,
          DirectSum.of (fun i : Int => Γ(P.tensorTwist F i, ⊤)) m y) =
      DirectSum.of (fun i : Int => Γ(P.tensorTwist F i, ⊤)) ((n : Int) + m)
        (AlgebraicGeometry.ProjTwistGlobalSections.homogeneousAction
          calA P mul F n m x y))
