/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.DirectSum.Ring
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.GlobalSections

/-!
# Section rings of chosen twists on projective spectra

An explicit graded commutative-ring structure on the global sections of a chosen family of
twists produces the canonical map from a nonnegatively graded ring to its twist section ring.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ProjTwistGlobalSections

variable {A sigma : Type u} [CommRing A] [SetLike sigma A] [AddSubgroupClass sigma A]
variable (calA : Nat -> sigma) [GradedRing calA]

/-- Explicit graded commutative-ring data on the global sections of an integral twist family,
compatible with a unit, homogeneous multiplication, and homogeneous section maps. -/
structure RingStructure where
  /-- The integral family of twists whose global sections form the homogeneous pieces. -/
  twist : ProjTwistFamily calA
  /-- The canonical additive map from each homogeneous piece to the corresponding global
  sections. -/
  sectionMap : ∀ n : Nat,
    AddCommGrpCat.of (calA n) ⟶ AddCommGrpCat.of (degree calA twist n)
  /-- The selected degree-zero global section. -/
  oneSection : degree calA twist 0
  /-- The selected homogeneous multiplication of global sections. -/
  sectionMul : ∀ m n : Nat,
    degree calA twist m → degree calA twist n → degree calA twist (m + n)
  /-- The graded commutative-ring structure on the homogeneous global sections. -/
  gradedCommRing : DirectSum.GCommRing (degree calA twist)
  /-- The graded unit is the selected degree-zero global section. -/
  one_eq :
    gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one = oneSection
  /-- The graded multiplication is the selected homogeneous multiplication. -/
  mul_eq : ∀ {m n : Nat} (x : degree calA twist m)
      (y : degree calA twist n),
    gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul x y =
      sectionMul m n x y
  /-- The degree-zero section map preserves the selected unit. -/
  map_one :
    DirectSum.of (degree calA twist) 0
        ((AddCommGrpCat.Hom.hom (sectionMap 0)) (1 : calA 0)) =
      DirectSum.of (degree calA twist) 0
        gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one
  /-- The homogeneous section maps preserve the selected multiplication. -/
  map_mul : ∀ {m n : Nat} (x : calA m) (y : calA n),
    DirectSum.of (degree calA twist) (m + n)
        ((AddCommGrpCat.Hom.hom (sectionMap (m + n)))
          ((SetLike.gMul calA).mul x y)) =
      DirectSum.of (degree calA twist) (m + n)
        (gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul
          ((AddCommGrpCat.Hom.hom (sectionMap m)) x)
          ((AddCommGrpCat.Hom.hom (sectionMap n)) y))

/-- The canonical map from a homogeneous piece to the global sections of the corresponding
twist. -/
abbrev degreeMap (R : RingStructure calA) (n : Nat) :
    AddCommGrpCat.of (calA n) ⟶ AddCommGrpCat.of (degree calA R.twist n) :=
  R.sectionMap n

/-- The direct sum of the nonnegative-degree global sections of an integral twist family. -/
abbrev ring (R : RingStructure calA) : Type u :=
  ⨁ n : Nat, degree calA R.twist n

/-- The selected degree-zero global section. -/
abbrev one (R : RingStructure calA) : degree calA R.twist 0 :=
  R.oneSection

/-- The selected homogeneous multiplication of global sections. -/
abbrev mul (R : RingStructure calA) (m n : Nat) :
    degree calA R.twist m →
      degree calA R.twist n →
        degree calA R.twist (m + n) :=
  R.sectionMul m n

/-- The compatibility conditions supplied by explicit projective-twist section-ring data. -/
theorem RingStructure.spec (R : RingStructure calA) :
    R.gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one = one calA R ∧
      (∀ {m n : Nat} (x : degree calA R.twist m)
          (y : degree calA R.twist n),
        R.gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul x y =
          mul calA R m n x y) ∧
      DirectSum.of (degree calA R.twist) 0
          ((AddCommGrpCat.Hom.hom (degreeMap calA R 0)) (1 : calA 0)) =
        DirectSum.of (degree calA R.twist) 0
          R.gradedCommRing.toGRing.toGSemiring.toGMonoid.toGOne.one ∧
      (∀ {m n : Nat} (x : calA m) (y : calA n),
        DirectSum.of (degree calA R.twist) (m + n)
            ((AddCommGrpCat.Hom.hom (degreeMap calA R (m + n)))
              ((SetLike.gMul calA).mul x y)) =
          DirectSum.of (degree calA R.twist) (m + n)
            (R.gradedCommRing.toGRing.toGSemiring.toGNonUnitalNonAssocSemiring.toGMul.mul
              ((AddCommGrpCat.Hom.hom (degreeMap calA R m)) x)
              ((AddCommGrpCat.Hom.hom (degreeMap calA R n)) y))) := sorry

/-- The commutative ring of nonnegative-degree global sections determined by explicit graded
ring data on an integral twist family. -/
noncomputable def sectionRing (R : RingStructure calA) : CommRingCat :=
  -- Local instance justification (defeq pin): the explicit RingStructure datum is passed to mathlib's class-parameterized DirectSum constructor.
  letI : DirectSum.GCommRing (degree calA R.twist) := R.gradedCommRing
  CommRingCat.of (ring calA R)

/-- The canonical map from the original graded ring to the section ring of the chosen twists. -/
noncomputable def gradedRingMap (R : RingStructure calA) :
    CommRingCat.of A ⟶ sectionRing calA R :=
  -- Local instance justification (defeq pin): the explicit RingStructure datum is passed to mathlib's class-parameterized DirectSum constructor.
  letI : DirectSum.GCommRing (degree calA R.twist) := R.gradedCommRing
  CommRingCat.ofHom <|
    (DirectSum.toSemiring
        (fun n ↦
          (DirectSum.of (degree calA R.twist) n).comp
            (AddCommGrpCat.Hom.hom (degreeMap calA R n)))
        R.map_one
        (fun {m n} x y ↦
          (R.map_mul x y).trans <|
            (DirectSum.of_mul_of (A := degree calA R.twist)
              ((AddCommGrpCat.Hom.hom (degreeMap calA R m)) x)
              ((AddCommGrpCat.Hom.hom (degreeMap calA R n)) y)).symm)).comp
      (DirectSum.decomposeRingEquiv calA).toRingHom

/-- The canonical graded-ring map sends a pure homogeneous element to its canonical global
section in the same degree. -/
theorem gradedRingMap_of (R : RingStructure calA) (n : Nat) (x : calA n) :
    gradedRingMap calA R x =
      DirectSum.of (degree calA R.twist) n
        ((AddCommGrpCat.Hom.hom (degreeMap calA R n)) x) := sorry

end AlgebraicGeometry.ProjTwistGlobalSections
