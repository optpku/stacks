/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.SectionRing

@[expose] public section

open CategoryTheory
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {A sigma : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable (calA : Nat -> sigma) [GradedRing calA]
variable (R : ProjTwistGlobalSections.RingStructure calA)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist :
    (n : Nat) → Type u)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R :
    (n : Nat) →
      AddCommGrpCat.of (calA n) ⟶
        AddCommGrpCat.of
          (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist n))

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.ring calA R : Type u)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.one calA R :
    AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist 0)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.mul calA R :
    (m n : Nat) →
      AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist m →
        AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist n →
          AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist (m + n))

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.RingStructure.gradedCommRing R :
    DirectSum.GCommRing
      (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist))

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.RingStructure calA : Type (u + 1))

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.RingStructure.one_eq R :
    R.gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one =
      AlgebraicGeometry.ProjTwistGlobalSections.one calA R)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.RingStructure.mul_eq R :
    ∀ {m n : Nat}
        (x : AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist m)
        (y : AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist n),
      R.gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul x y =
        AlgebraicGeometry.ProjTwistGlobalSections.mul calA R m n x y)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.RingStructure.map_one R :
    DirectSum.of
        (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) 0
        ((AddCommGrpCat.Hom.hom
          (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R 0))
            (1 : calA 0)) =
      DirectSum.of
        (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) 0
        R.gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.RingStructure.map_mul R :
    ∀ {m n : Nat} (x : calA m) (y : calA n),
      DirectSum.of
          (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) (m + n)
          ((AddCommGrpCat.Hom.hom
            (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R (m + n)))
              ((SetLike.gMul calA).mul x y)) =
        DirectSum.of
          (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) (m + n)
          (R.gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul
            ((AddCommGrpCat.Hom.hom
              (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R m)) x)
            ((AddCommGrpCat.Hom.hom
              (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R n)) y)))

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.RingStructure.spec calA R :
    R.gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one =
        AlgebraicGeometry.ProjTwistGlobalSections.one calA R ∧
      (∀ {m n : Nat}
          (x : AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist m)
          (y : AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist n),
        R.gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul x y =
          AlgebraicGeometry.ProjTwistGlobalSections.mul calA R m n x y) ∧
      DirectSum.of
          (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) 0
          ((AddCommGrpCat.Hom.hom
            (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R 0))
              (1 : calA 0)) =
        DirectSum.of
          (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) 0
          R.gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one ∧
      (∀ {m n : Nat} (x : calA m) (y : calA n),
        DirectSum.of
            (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) (m + n)
            ((AddCommGrpCat.Hom.hom
              (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R (m + n)))
                ((SetLike.gMul calA).mul x y)) =
          DirectSum.of
            (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) (m + n)
            (R.gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul
              ((AddCommGrpCat.Hom.hom
                (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R m)) x)
              ((AddCommGrpCat.Hom.hom
                (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R n)) y))))

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.sectionRing calA R : CommRingCat)

#check
  (AlgebraicGeometry.ProjTwistGlobalSections.gradedRingMap_of calA R :
    ∀ (n : Nat) (x : calA n),
      AlgebraicGeometry.ProjTwistGlobalSections.gradedRingMap calA R x =
        DirectSum.of
          (AlgebraicGeometry.ProjTwistGlobalSections.degree calA R.twist) n
          ((AddCommGrpCat.Hom.hom
            (AlgebraicGeometry.ProjTwistGlobalSections.degreeMap calA R n)) x))

/-
27.10.1.3: The canonical graded-ring map from a nonnegatively graded ring to the direct sum of
the global sections of its chosen genuine twists on `Proj calA`.
-/
@[stacks 01MP] #check
  (AlgebraicGeometry.ProjTwistGlobalSections.gradedRingMap calA R :
    CommRingCat.of A ⟶
      AlgebraicGeometry.ProjTwistGlobalSections.sectionRing calA R)

end

end AlgebraicGeometry
