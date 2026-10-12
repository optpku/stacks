/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.GroupoidScheme
public import ReasLib.AlgebraicGeometry.Scheme.Over.CartesianMonoidal
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation.Stabilizer

/-!
# Stabilizer groups of groupoid schemes

This module equips the diagonal pullback stabilizer of a groupoid scheme with its canonical
group-object structure.
-/

@[expose] public section

open CategoryTheory Limits
open CartesianMonoidalCategory MonoidalCategory MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The two arrows underlying a pair of stabilizer elements are composable. -/
theorem stabilizerComposablePair_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    ((fst G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
          G.toPreRelation.stabilizerToArrows) ≫ G.s =
      ((snd G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
          G.toPreRelation.stabilizerToArrows) ≫ G.t := sorry

/-- The composable pair of arrows underlying two stabilizer elements. -/
def stabilizerComposablePair {S : Scheme.{u}} (G : GroupoidScheme S) :
    (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).left ⟶
      pullback G.s G.t :=
  pullback.lift
    ((fst G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
      G.toPreRelation.stabilizerToArrows)
    ((snd G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
      G.toPreRelation.stabilizerToArrows)
    (stabilizerComposablePair_condition G)

/-- The first projection of `stabilizerComposablePair G` is the first stabilizer arrow. -/
theorem stabilizerComposablePair_fst {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerComposablePair G ≫ pullback.fst G.s G.t =
      (fst G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
        G.toPreRelation.stabilizerToArrows := sorry

/-- The second projection of `stabilizerComposablePair G` is the second stabilizer arrow. -/
theorem stabilizerComposablePair_snd {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerComposablePair G ≫ pullback.snd G.s G.t =
      (snd G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
        G.toPreRelation.stabilizerToArrows := sorry

/-- Groupoid composition and the common base point define stabilizer multiplication. -/
theorem stabilizerMul_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizerComposablePair G ≫ G.c) ≫ G.toPreRelation.hom =
      (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).hom ≫ diag G.U := sorry

/-- The underlying pullback lift defining multiplication on the stabilizer. -/
def stabilizerMulLift {S : Scheme.{u}} (G : GroupoidScheme S) :
    (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).left ⟶
      G.toPreRelation.stabilizer.left :=
  pullback.lift (stabilizerComposablePair G ≫ G.c)
    (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).hom
    (stabilizerMul_condition G)

/-- The stabilizer multiplication lift lies over the object scheme. -/
theorem stabilizerMulLift_over {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerMulLift G ≫ G.toPreRelation.stabilizer.hom =
      (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).hom := sorry

/-- Multiplication on the stabilizer induced by groupoid composition. -/
def stabilizerMul {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer ⟶
      G.toPreRelation.stabilizer :=
  Over.homMk (stabilizerMulLift G) (stabilizerMulLift_over G)

/-- Stabilizer multiplication followed by the map to arrows is groupoid composition. -/
theorem stabilizerMul_toArrows {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizerMul G).left ≫ G.toPreRelation.stabilizerToArrows =
      stabilizerComposablePair G ≫ G.c := sorry

/-- The groupoid identity and the identity base map define a stabilizer element. -/
theorem stabilizerOne_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.e ≫ G.toPreRelation.hom = 𝟙 G.U ≫ diag G.U := sorry

/-- The underlying pullback lift defining the unit of the stabilizer. -/
def stabilizerOneLift {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.U ⟶ G.toPreRelation.stabilizer.left :=
  pullback.lift G.e (𝟙 G.U) (stabilizerOne_condition G)

/-- The stabilizer unit lift lies over the object scheme. -/
theorem stabilizerOneLift_over {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerOneLift G ≫ G.toPreRelation.stabilizer.hom =
      (𝟙_ (Over G.U)).hom := sorry

/-- The unit of the stabilizer induced by the groupoid identity. -/
def stabilizerOne {S : Scheme.{u}} (G : GroupoidScheme S) :
    𝟙_ (Over G.U) ⟶ G.toPreRelation.stabilizer :=
  Over.homMk (stabilizerOneLift G) (stabilizerOneLift_over G)

/-- The stabilizer unit followed by the map to arrows is the groupoid identity. -/
theorem stabilizerOne_toArrows {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizerOne G).left ≫ G.toPreRelation.stabilizerToArrows = G.e := sorry

/-- Groupoid inversion and the stabilizer base map define a stabilizer element. -/
theorem stabilizerInv_condition {S : Scheme.{u}} (G : GroupoidScheme S) :
    (G.toPreRelation.stabilizerToArrows ≫ G.i) ≫ G.toPreRelation.hom =
      G.toPreRelation.stabilizer.hom ≫ diag G.U := sorry

/-- The underlying pullback lift defining inversion on the stabilizer. -/
def stabilizerInvLift {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.stabilizer.left ⟶ G.toPreRelation.stabilizer.left :=
  pullback.lift (G.toPreRelation.stabilizerToArrows ≫ G.i)
    G.toPreRelation.stabilizer.hom (stabilizerInv_condition G)

/-- The stabilizer inversion lift lies over the object scheme. -/
theorem stabilizerInvLift_over {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerInvLift G ≫ G.toPreRelation.stabilizer.hom =
      G.toPreRelation.stabilizer.hom := sorry

/-- Inversion on the stabilizer induced by groupoid inversion. -/
def stabilizerInv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.stabilizer ⟶ G.toPreRelation.stabilizer :=
  Over.homMk (stabilizerInvLift G) (stabilizerInvLift_over G)

/-- Stabilizer inversion followed by the map to arrows is groupoid inversion. -/
theorem stabilizerInv_toArrows {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizerInv G).left ≫ G.toPreRelation.stabilizerToArrows =
      G.toPreRelation.stabilizerToArrows ≫ G.i := sorry

/-- The induced unit is a left unit for stabilizer multiplication. -/
theorem stabilizerOneMul {S : Scheme.{u}} (G : GroupoidScheme S) :
    stabilizerOne G ▷ G.toPreRelation.stabilizer ≫ stabilizerMul G =
      (λ_ G.toPreRelation.stabilizer).hom := sorry

/-- The induced unit is a right unit for stabilizer multiplication. -/
theorem stabilizerMulOne {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.toPreRelation.stabilizer ◁ stabilizerOne G ≫ stabilizerMul G =
      (ρ_ G.toPreRelation.stabilizer).hom := sorry

/-- Stabilizer multiplication is associative. -/
theorem stabilizerMulAssoc {S : Scheme.{u}} (G : GroupoidScheme S) :
    (stabilizerMul G ▷ G.toPreRelation.stabilizer) ≫ stabilizerMul G =
      (α_ G.toPreRelation.stabilizer G.toPreRelation.stabilizer
          G.toPreRelation.stabilizer).hom ≫
        (G.toPreRelation.stabilizer ◁ stabilizerMul G) ≫ stabilizerMul G := sorry

/-- The induced inverse satisfies the left inverse law. -/
theorem stabilizerLeftInv {S : Scheme.{u}} (G : GroupoidScheme S) :
    lift (stabilizerInv G) (𝟙 G.toPreRelation.stabilizer) ≫ stabilizerMul G =
      toUnit G.toPreRelation.stabilizer ≫ stabilizerOne G := sorry

/-- The induced inverse satisfies the right inverse law. -/
theorem stabilizerRightInv {S : Scheme.{u}} (G : GroupoidScheme S) :
    lift (𝟙 G.toPreRelation.stabilizer) (stabilizerInv G) ≫ stabilizerMul G =
      toUnit G.toPreRelation.stabilizer ≫ stabilizerOne G := sorry

/-- The explicit group-object structure carried by the stabilizer of a groupoid scheme. -/
@[reducible]
def stabilizerGroupObject {S : Scheme.{u}} (G : GroupoidScheme S) :
    GrpObj G.toPreRelation.stabilizer where
  one := stabilizerOne G
  mul := stabilizerMul G
  one_mul := stabilizerOneMul G
  mul_one := stabilizerMulOne G
  mul_assoc := stabilizerMulAssoc G
  inv := stabilizerInv G
  left_inv := stabilizerLeftInv G
  right_inv := stabilizerRightInv G

/-- The stabilizer of a groupoid scheme as a bundled group object over its object scheme. -/
def stabilizer {S : Scheme.{u}} (G : GroupoidScheme S) : Grp (Over G.U) :=
  { X := G.toPreRelation.stabilizer
    grp := stabilizerGroupObject G }

/-- The carrier of the stabilizer group is the diagonal pullback. -/
theorem stabilizer_X {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizer.X = G.toPreRelation.stabilizer := sorry

/-- Stabilizer multiplication is induced by groupoid composition. -/
theorem stabilizer_mul {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizer.grp.mul = stabilizerMul G := sorry

/-- The stabilizer unit is induced by the groupoid identity. -/
theorem stabilizer_one {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizer.grp.one = stabilizerOne G := sorry

/-- Stabilizer inversion is induced by groupoid inversion. -/
theorem stabilizer_inv {S : Scheme.{u}} (G : GroupoidScheme S) :
    G.stabilizer.grp.inv = stabilizerInv G := sorry

end AlgebraicGeometry.GroupoidScheme
