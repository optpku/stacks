module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Group
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.CategoryTheory.Sites.Torsor.Basic

/-!
# The sheaf of relative points of a group algebraic space
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.AlgebraicSpace
open CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)

/-- The morphism `ofOver V ⟶ G` over `B` associated to a fibre point. -/
def FiberPoint.asOverHom {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) :
    Over.mk (ofOverMap (overMapHom V) ≫ b) ⟶ G.X :=
  Over.homMk (yonedaEquiv.symm x.val) sorry

/-- Multiplication of fibre points uses the multiplication of `G`. -/
def FiberPoint.mul {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x y : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) }) where
  val := yonedaEquiv ((lift (FiberPoint.asOverHom G x) (FiberPoint.asOverHom G y)).left ≫ μ[G.X].left)
  property := sorry

/-- The identity fibre point is the unit of `G` pulled back along `b`. -/
def FiberPoint.one {U : Over S} {b : ofOver U ⟶ B} (V : Over U.left) :
    ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) }) where
  val :=
    yonedaEquiv
      ((toUnit (Over.mk (ofOverMap (overMapHom V) ≫ b))).left ≫ η[G.X].left)
  property := sorry

/-- Inversion of fibre points uses the inverse of `G`. -/
def FiberPoint.inv {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) }) where
  val := yonedaEquiv ((FiberPoint.asOverHom G x).left ≫ ι[G.X].left)
  property := sorry

/-- Associativity of multiplication of fibre points. -/
theorem FiberPoint.mul_assoc {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x y z : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) :
    FiberPoint.mul G (FiberPoint.mul G x y) z =
      FiberPoint.mul G x (FiberPoint.mul G y z) := sorry

/-- Left unit law for fibre points. -/
theorem FiberPoint.one_mul {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) :
    FiberPoint.mul G (FiberPoint.one G V) x = x := sorry

/-- Right unit law for fibre points. -/
theorem FiberPoint.mul_one {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) :
    FiberPoint.mul G x (FiberPoint.one G V) = x := sorry

/-- Left inverse law for fibre points. -/
theorem FiberPoint.inv_mul_cancel {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) :
    FiberPoint.mul G (FiberPoint.inv G x) x = FiberPoint.one G V := sorry

/-- Fibre points of `G` over `b` form a group. -/
@[reducible]
def instGroup_fiberPoint {U : Over S} (b : ofOver U ⟶ B) (V : Over U.left) :
    Group (({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })) where
  mul := FiberPoint.mul G
  one := FiberPoint.one G V
  inv := FiberPoint.inv G
  mul_assoc := FiberPoint.mul_assoc G
  one_mul := FiberPoint.one_mul G
  mul_one := FiberPoint.mul_one G
  inv_mul_cancel := FiberPoint.inv_mul_cancel G

/-- The group of points of the total space lying over the specified base point. -/
def fiberPointGrp {U : Over S} (b : ofOver U ⟶ B) (V : Over U.left) : GrpCat.{u} where
  carrier := ({ val : G.X.left.functorOfPoints.obj (op ((Over.map U.hom).obj V)) //
      G.X.hom.app (op ((Over.map U.hom).obj V)) val =
        yonedaEquiv (ofOverMap (overMapHom V) ≫ b) })
  str := instGroup_fiberPoint G b V

/-- The carrier of the group of relative points over a scheme. -/
abbrev FiberPoint {U : Over S} (b : ofOver U ⟶ B) (V : Over U.left) : Type u :=
  fiberPointGrp G b V

/-- A relative group point maps to the prescribed point of the base. -/
theorem FiberPoint.over_b {U : Over S} {b : ofOver U ⟶ B} {V : Over U.left}
    (x : FiberPoint G b V) :
    G.X.hom.app (op ((Over.map U.hom).obj V)) x.val =
      yonedaEquiv (ofOverMap (overMapHom V) ≫ b) := x.property

/-- Restriction of a fibre point along a morphism of schemes over `U`. -/
def FiberPoint.res {U : Over S} {b : ofOver U ⟶ B} {V W : Over U.left} (f : W ⟶ V)
    (x : FiberPoint G b V) : FiberPoint G b W where
  val := G.X.left.functorOfPoints.map ((Over.map U.hom).map f).op x.val
  property := sorry

/-- Restriction of fibre points is a group homomorphism. -/
def FiberPoint.resHom {U : Over S} {b : ofOver U ⟶ B} {V W : Over U.left} (f : W ⟶ V) :
    FiberPoint G b V →* FiberPoint G b W where
  toFun := FiberPoint.res G f
  map_one' := sorry
  map_mul' := sorry

/-- The group-valued presheaf of points of `U ×_{b,ℬ} 𝒢`. -/
def baseChangePresheaf {U : Over S} (b : ofOver U ⟶ B) :
    (Over U.left)ᵒᵖ ⥤ GrpCat.{u} where
  obj V := fiberPointGrp G b V.unop
  map {V W} f := ConcreteCategory.ofHom (C := GrpCat) (FiberPoint.resHom G f.unop)
  map_id := sorry
  map_comp := sorry

/-- The group-valued presheaf of points of `U ×_{b,ℬ} 𝒢` is an fppf sheaf. -/
theorem baseChangePresheaf_isSheaf {U : Over S} (b : ofOver U ⟶ B) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over U.left) (baseChangePresheaf G b) := sorry

/-- The fppf sheaf of groups `U ×_{b,ℬ} 𝒢` on `(Sch/U)_fppf`. -/
def baseChangeGroupSheaf {U : Over S} (b : ofOver U ⟶ B) :
    Sheaf (Scheme.fppfTopology.over U.left) GrpCat.{u} where
  obj := baseChangePresheaf G b
  property := baseChangePresheaf_isSheaf G b

/-- The underlying group-valued presheaf of `baseChangeGroupSheaf` is
`baseChangePresheaf`. -/
theorem baseChangeGroupSheaf_obj {U : Over S} (b : ofOver U ⟶ B) :
    (baseChangeGroupSheaf G b).obj = baseChangePresheaf G b := sorry

/-- Group sections of `U ×_{b,ℬ} 𝒢` and of `U' ×_{b',ℬ} 𝒢` agree after inverse
image along `f`. -/
def groupMulEquiv {U U' : Over S} (f : U ⟶ U') (b' : ofOver U' ⟶ B)
    (V : Over U.left) :
    FiberPoint G (ofOverMap f ≫ b') V ≃*
      FiberPoint G b' ((Over.map f.left).obj V) where
  toEquiv :=
    { toFun x :=
        { val := G.X.left.functorOfPoints.map (baseOverIso f V).symm.hom.op x.val
          property := sorry }
      invFun x :=
        { val := G.X.left.functorOfPoints.map (baseOverIso f V).hom.op x.val
          property := sorry }
      left_inv := sorry
      right_inv := sorry }
  map_mul' := sorry

/-- Transport a fibre point along an equality of morphisms to `B`. -/
def FiberPoint.transport {U : Over S} {b b' : ofOver U ⟶ B} (h : b = b')
    {V : Over U.left} (x : FiberPoint G b V) : FiberPoint G b' V :=
  h ▸ x

end AlgebraicGeometry.GroupAlgebraicSpace.SheafTorsors
