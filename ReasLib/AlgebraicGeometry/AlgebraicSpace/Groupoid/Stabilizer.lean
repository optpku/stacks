/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CartesianMonoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation
/-!
# Stabilizer groups of groupoids in algebraic spaces

This module equips the diagonal pullback stabilizer of a groupoid in algebraic
spaces with its canonical group-object structure.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The morphism `j = (t, s)` from arrows to the fibre product of objects. -/
def j {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.R ⟶ G.U ⨯ G.U :=
  prod.lift G.t G.s

/-- The morphism `j` is the product lift of the target and source maps. -/
theorem j_eq_prod_lift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.j = prod.lift G.t G.s := sorry

/-- Forget a groupoid in algebraic spaces to its underlying pre-relation, with defining
map `(t, s)`. -/
def toPreRelation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : AlgebraicSpace.PreRelation G.U :=
  AlgebraicSpace.PreRelation.ofHom G.j

/-- The target projection of the underlying pre-relation is the target map. -/
theorem toPreRelation_t {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.t = G.t := sorry

/-- The source projection of the underlying pre-relation is the source map. -/
theorem toPreRelation_s {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.s = G.s := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- The stabilizer of a pre-relation is its pullback along the diagonal. -/
def stabilizer {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : Over U :=
  (Over.pullback (diag U)).obj P

/-- The carrier of the stabilizer is the pullback of the relation map along the diagonal. -/
theorem stabilizer_left {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.stabilizer.left = Limits.pullback P.hom (diag U) := sorry

/-- The structure map of the stabilizer is the second pullback projection. -/
theorem stabilizer_hom {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    P.stabilizer.hom = Limits.pullback.snd P.hom (diag U) := sorry

/-- The canonical map from the stabilizer to the arrow object of the pre-relation. -/
def stabilizerToArrows {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) : P.stabilizer.left ⟶ P.left :=
  Limits.pullback.fst P.hom (diag U)

/-- The maps from the stabilizer to the arrows and to `U` form its defining pullback square. -/
theorem stabilizerToArrows_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U : Over B} (P : PreRelation U) :
    P.stabilizerToArrows ≫ P.hom = P.stabilizer.hom ≫ diag U := sorry

/-- The stabilizer square is a pullback of the relation map along the diagonal. -/
theorem stabilizer_isPullback {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) :
    IsPullback P.stabilizerToArrows P.stabilizer.hom P.hom (diag U) := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
namespace AlgebraicGeometry.GroupoidAlgebraicSpace

open CartesianMonoidalCategory MonoidalCategory MonObj

/-- The two arrows underlying a pair of stabilizer elements are composable. -/
theorem stabilizerComposablePair_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    ((fst G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
          G.toPreRelation.stabilizerToArrows) ≫ G.s =
      ((snd G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
          G.toPreRelation.stabilizerToArrows) ≫ G.t := sorry

/-- The composable pair of arrows underlying two stabilizer elements. -/
def stabilizerComposablePair {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).left ⟶ pullback G.s G.t :=
  pullback.lift
    ((fst G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
      G.toPreRelation.stabilizerToArrows)
    ((snd G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
      G.toPreRelation.stabilizerToArrows)
    (stabilizerComposablePair_condition G)

/-- The first projection of `stabilizerComposablePair G` is the first stabilizer arrow. -/
theorem stabilizerComposablePair_fst {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    stabilizerComposablePair G ≫ pullback.fst G.s G.t =
      (fst G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
        G.toPreRelation.stabilizerToArrows := sorry

/-- The second projection of `stabilizerComposablePair G` is the second stabilizer arrow. -/
theorem stabilizerComposablePair_snd {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    stabilizerComposablePair G ≫ pullback.snd G.s G.t =
      (snd G.toPreRelation.stabilizer G.toPreRelation.stabilizer).left ≫
        G.toPreRelation.stabilizerToArrows := sorry

/-- Groupoid composition and the common base point define stabilizer multiplication. -/
theorem stabilizerMul_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stabilizerComposablePair G ≫ G.c) ≫ G.toPreRelation.hom =
      (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).hom ≫
        Limits.diag G.U := sorry

/-- The underlying pullback lift defining multiplication on the stabilizer. -/
def stabilizerMulLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).left ⟶
      G.toPreRelation.stabilizer.left :=
  pullback.lift (stabilizerComposablePair G ≫ G.c)
    (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).hom
    (stabilizerMul_condition G)

/-- The stabilizer multiplication lift lies over the object space. -/
theorem stabilizerMulLift_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    stabilizerMulLift G ≫ G.toPreRelation.stabilizer.hom =
      (G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer).hom := sorry

/-- Multiplication on the stabilizer induced by groupoid composition. -/
def stabilizerMul {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.stabilizer ⊗ G.toPreRelation.stabilizer ⟶
      G.toPreRelation.stabilizer :=
  Over.homMk (stabilizerMulLift G) (stabilizerMulLift_over G)

/-- Stabilizer multiplication followed by the map to arrows is groupoid composition. -/
theorem stabilizerMul_toArrows {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stabilizerMul G).left ≫ G.toPreRelation.stabilizerToArrows =
      stabilizerComposablePair G ≫ G.c := sorry

/-- The groupoid identity and the identity base map define a stabilizer element. -/
theorem stabilizerOne_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.e ≫ G.toPreRelation.hom = 𝟙 G.U ≫ Limits.diag G.U := sorry

/-- The underlying pullback lift defining the unit of the stabilizer. -/
def stabilizerOneLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.U ⟶ G.toPreRelation.stabilizer.left :=
  pullback.lift G.e (𝟙 G.U) (stabilizerOne_condition G)

/-- The stabilizer unit lift lies over the object space. -/
theorem stabilizerOneLift_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    stabilizerOneLift G ≫ G.toPreRelation.stabilizer.hom =
      (𝟙_ (Over G.U)).hom := sorry

/-- The unit of the stabilizer induced by the groupoid identity. -/
def stabilizerOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    𝟙_ (Over G.U) ⟶ G.toPreRelation.stabilizer :=
  Over.homMk (stabilizerOneLift G) (stabilizerOneLift_over G)

/-- The stabilizer unit followed by the map to arrows is the groupoid identity. -/
theorem stabilizerOne_toArrows {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stabilizerOne G).left ≫ G.toPreRelation.stabilizerToArrows = G.e := sorry

/-- Groupoid inversion and the stabilizer base map define a stabilizer element. -/
theorem stabilizerInv_condition {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (G.toPreRelation.stabilizerToArrows ≫ G.i) ≫ G.toPreRelation.hom =
      G.toPreRelation.stabilizer.hom ≫ Limits.diag G.U := sorry

/-- The underlying pullback lift defining inversion on the stabilizer. -/
def stabilizerInvLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.stabilizer.left ⟶ G.toPreRelation.stabilizer.left :=
  pullback.lift (G.toPreRelation.stabilizerToArrows ≫ G.i)
    G.toPreRelation.stabilizer.hom (stabilizerInv_condition G)

/-- The stabilizer inversion lift lies over the object space. -/
theorem stabilizerInvLift_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    stabilizerInvLift G ≫ G.toPreRelation.stabilizer.hom =
      G.toPreRelation.stabilizer.hom := sorry

/-- Inversion on the stabilizer induced by groupoid inversion. -/
def stabilizerInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.stabilizer ⟶ G.toPreRelation.stabilizer :=
  Over.homMk (stabilizerInvLift G) (stabilizerInvLift_over G)

/-- Stabilizer inversion followed by the map to arrows is groupoid inversion. -/
theorem stabilizerInv_toArrows {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stabilizerInv G).left ≫ G.toPreRelation.stabilizerToArrows =
      G.toPreRelation.stabilizerToArrows ≫ G.i := sorry

/-- The induced unit is a left unit for stabilizer multiplication. -/
theorem stabilizerOneMul {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    stabilizerOne G ▷ G.toPreRelation.stabilizer ≫ stabilizerMul G =
      (λ_ G.toPreRelation.stabilizer).hom := sorry

/-- The induced unit is a right unit for stabilizer multiplication. -/
theorem stabilizerMulOne {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.toPreRelation.stabilizer ◁ stabilizerOne G ≫ stabilizerMul G =
      (ρ_ G.toPreRelation.stabilizer).hom := sorry

/-- Stabilizer multiplication is associative. -/
theorem stabilizerMulAssoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stabilizerMul G ▷ G.toPreRelation.stabilizer) ≫ stabilizerMul G =
      (α_ G.toPreRelation.stabilizer G.toPreRelation.stabilizer
          G.toPreRelation.stabilizer).hom ≫
        (G.toPreRelation.stabilizer ◁ stabilizerMul G) ≫ stabilizerMul G := sorry

/-- The induced inverse satisfies the left inverse law. -/
theorem stabilizerLeftInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    lift (stabilizerInv G) (𝟙 G.toPreRelation.stabilizer) ≫ stabilizerMul G =
      toUnit G.toPreRelation.stabilizer ≫ stabilizerOne G := sorry

/-- The induced inverse satisfies the right inverse law. -/
theorem stabilizerRightInv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    lift (𝟙 G.toPreRelation.stabilizer) (stabilizerInv G) ≫ stabilizerMul G =
      toUnit G.toPreRelation.stabilizer ≫ stabilizerOne G := sorry

/-- The explicit group-object structure carried by the stabilizer of a groupoid in
algebraic spaces. -/
@[reducible]
def stabilizerGroupObject {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : GrpObj G.toPreRelation.stabilizer where
  one := stabilizerOne G
  mul := stabilizerMul G
  one_mul := stabilizerOneMul G
  mul_one := stabilizerMulOne G
  mul_assoc := stabilizerMulAssoc G
  inv := stabilizerInv G
  left_inv := stabilizerLeftInv G
  right_inv := stabilizerRightInv G

/-- The stabilizer of a groupoid in algebraic spaces as a bundled group object over its
object space. -/
def stabilizer {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : Grp (Over G.U) :=
  { X := G.toPreRelation.stabilizer
    grp := stabilizerGroupObject G }

/-- The carrier of the stabilizer group is the diagonal pullback. -/
theorem stabilizer_X {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.stabilizer.X = G.toPreRelation.stabilizer := sorry

/-- Stabilizer multiplication is induced by groupoid composition. -/
theorem stabilizer_mul {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.stabilizer.grp.mul = stabilizerMul G := sorry

/-- The stabilizer unit is induced by the groupoid identity. -/
theorem stabilizer_one {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.stabilizer.grp.one = stabilizerOne G := sorry

/-- Stabilizer inversion is induced by groupoid inversion. -/
theorem stabilizer_inv {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.stabilizer.grp.inv = stabilizerInv G := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
