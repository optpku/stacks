/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid

/-! Groupoids in algebraic spaces associated to group algebraic spaces. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

variable {S : Scheme.{u}}

/-- The composition morphism induced by multiplication in a group algebraic space. -/
def groupComposition {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    pullback (toUnit G.X) (toUnit G.X) ⟶ G.X :=
  lift (pullback.fst (toUnit G.X) (toUnit G.X))
    (pullback.snd (toUnit G.X) (toUnit G.X)) ≫ μ[G.X]

/-- Multiplication in a group algebraic space is associative on compatible points. -/
theorem groupComposition_assoc {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    ∀ {T : Over B} (a b d : T ⟶ G.X)
      (h_ab : a ≫ toUnit G.X = b ≫ toUnit G.X)
      (h_bd : b ≫ toUnit G.X = d ≫ toUnit G.X)
      (h_ab_d : (pullback.lift a b h_ab ≫ groupComposition G) ≫ toUnit G.X =
        d ≫ toUnit G.X)
      (h_a_bd : a ≫ toUnit G.X =
        (pullback.lift b d h_bd ≫ groupComposition G) ≫ toUnit G.X),
      pullback.lift (pullback.lift a b h_ab ≫ groupComposition G) d h_ab_d ≫
          groupComposition G =
        pullback.lift a (pullback.lift b d h_bd ≫ groupComposition G) h_a_bd ≫
          groupComposition G := sorry

/-- Multiplication in a group algebraic space has a right identity. -/
theorem groupComposition_right_identity {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    ∀ {T : Over B} (a : T ⟶ G.X)
      (h : a ≫ toUnit G.X = ((a ≫ toUnit G.X) ≫ η[G.X]) ≫ toUnit G.X),
      pullback.lift a ((a ≫ toUnit G.X) ≫ η[G.X]) h ≫ groupComposition G = a :=
  sorry

/-- Multiplication in a group algebraic space has a left identity. -/
theorem groupComposition_left_identity {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    ∀ {T : Over B} (a : T ⟶ G.X)
      (h : ((a ≫ toUnit G.X) ≫ η[G.X]) ≫ toUnit G.X = a ≫ toUnit G.X),
      pullback.lift ((a ≫ toUnit G.X) ≫ η[G.X]) a h ≫ groupComposition G = a :=
  sorry

/-- Multiplication of an arrow with its inverse gives the identity. -/
theorem groupComposition_inverse_comp {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    ∀ {T : Over B} (a : T ⟶ G.X)
      (h : a ≫ toUnit G.X = (a ≫ ι[G.X]) ≫ toUnit G.X),
      pullback.lift a (a ≫ ι[G.X]) h ≫ groupComposition G =
        (a ≫ toUnit G.X) ≫ η[G.X] := sorry

/-- Multiplication of the inverse of an arrow with it gives the identity. -/
theorem groupComposition_comp_inverse {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) :
    ∀ {T : Over B} (a : T ⟶ G.X)
      (h : (a ≫ ι[G.X]) ≫ toUnit G.X = a ≫ toUnit G.X),
      pullback.lift (a ≫ ι[G.X]) a h ≫ groupComposition G =
        (a ≫ toUnit G.X) ≫ η[G.X] := sorry

/-- The one-object groupoid associated to a group algebraic space. -/
def ofGroup {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    GroupoidAlgebraicSpace B where
  U := 𝟙_ (Over B)
  R := G.X
  s := toUnit G.X
  t := toUnit G.X
  c := groupComposition G
  e := η[G.X]
  i := ι[G.X]
  comp_source := SemiCartesianMonoidalCategory.toUnit_unique _ _
  comp_target := SemiCartesianMonoidalCategory.toUnit_unique _ _
  identity_source := SemiCartesianMonoidalCategory.toUnit_unique _ _
  identity_target := SemiCartesianMonoidalCategory.toUnit_unique _ _
  inverse_source := SemiCartesianMonoidalCategory.toUnit_unique _ _
  inverse_target := SemiCartesianMonoidalCategory.toUnit_unique _ _
  associativity := groupComposition_assoc G
  right_identity := groupComposition_right_identity G
  left_identity := groupComposition_left_identity G
  inverse_comp := groupComposition_inverse_comp G
  comp_inverse := groupComposition_comp_inverse G

/-- The object space of the one-object groupoid is the cartesian unit over `B`. -/
theorem ofGroup_U {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).U = 𝟙_ (Over B) := sorry

/-- The arrow space of the one-object groupoid is the underlying object of `G`. -/
theorem ofGroup_R {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).R = G.X := sorry

/-- The source map of the one-object groupoid is the structure morphism of `G`. -/
theorem ofGroup_s {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).s = toUnit G.X := sorry

/-- The target map of the one-object groupoid is the structure morphism of `G`. -/
theorem ofGroup_t {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).t = toUnit G.X := sorry

/-- Source and target of the one-object groupoid coincide. -/
theorem ofGroup_s_eq_t {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).s = (ofGroup G).t := sorry

/-- The composition map of the one-object groupoid is the group law on `G ×_B G`. -/
theorem ofGroup_c {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).c = groupComposition G := sorry

/-- The identity map of the one-object groupoid is the unit of `G`. -/
theorem ofGroup_e {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).e = η[G.X] := sorry

/-- The inverse map of the one-object groupoid is the inversion of `G`. -/
theorem ofGroup_i {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) :
    (ofGroup G).i = ι[G.X] := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
