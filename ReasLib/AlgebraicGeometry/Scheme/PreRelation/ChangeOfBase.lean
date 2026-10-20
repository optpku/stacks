module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation
public import ReasLib.CategoryTheory.Limits.Over.Products

/-!
# Change of base for scheme pre-relations

Scheme pre-relations can be viewed over a new base or pulled back along a base morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.PreRelation

/-- View a pre-relation on `U` over `S` as a pre-relation on `U` over `S'` along `g : S ⟶ S'`,
by applying `Over.map g` and composing with the comparison `(U ⨯_S U) ⟶ (j U ⨯_{S'} j U)`. -/
def viewedOver {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S} (P : PreRelation U) :
    PreRelation ((Over.map g).obj U) :=
  ofHom ((Over.map g).map P.hom ≫ prodComparison (Over.map g) U U)

/-- The source of `viewedOver g P` is `P` viewed as a scheme over `S'`. -/
@[simp]
theorem viewedOver_left {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S}
    (P : PreRelation U) :
    (P.viewedOver g).left = (Over.map g).obj P.left := sorry

/-- The first projection of `viewedOver g P` is the image of `P.t` under `Over.map g`. -/
@[simp]
theorem viewedOver_t {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S} (P : PreRelation U) :
    (P.viewedOver g).t = (Over.map g).map P.t := sorry

/-- The second projection of `viewedOver g P` is the image of `P.s` under `Over.map g`. -/
@[simp]
theorem viewedOver_s {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S} (P : PreRelation U) :
    (P.viewedOver g).s = (Over.map g).map P.s := sorry

/-- The underlying scheme morphism of the first projection of `viewedOver g P` agrees with
that of `P.t`. -/
theorem viewedOver_t_left {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S}
    (P : PreRelation U) :
    (P.viewedOver g).t.left = P.t.left := sorry

/-- The underlying scheme morphism of the second projection of `viewedOver g P` agrees with
that of `P.s`. -/
theorem viewedOver_s_left {S S' : Scheme.{u}} (g : S ⟶ S') {U : Over S}
    (P : PreRelation U) :
    (P.viewedOver g).s.left = P.s.left := sorry

/-- Base change a pre-relation on `U'` over `S'` to a pre-relation on `U'_S` over `S`, by
applying `Over.pullback g` and the product comparison. -/
def baseChange {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'} (P : PreRelation U') :
    PreRelation ((Over.pullback g).obj U') :=
  ofHom ((Over.pullback g).map P.hom ≫ prodComparison (Over.pullback g) U' U')

/-- The source of `baseChange g P` is the pullback of the source of `P` along `g`. -/
@[simp]
theorem baseChange_left {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'}
    (P : PreRelation U') :
    (P.baseChange g).left = (Over.pullback g).obj P.left := sorry

/-- The first projection of `baseChange g P` is the image of `P.t` under `Over.pullback g`. -/
@[simp]
theorem baseChange_t {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'}
    (P : PreRelation U') :
    (P.baseChange g).t = (Over.pullback g).map P.t := sorry

/-- The second projection of `baseChange g P` is the image of `P.s` under `Over.pullback g`. -/
@[simp]
theorem baseChange_s {S S' : Scheme.{u}} (g : S ⟶ S') {U' : Over S'}
    (P : PreRelation U') :
    (P.baseChange g).s = (Over.pullback g).map P.s := sorry

end AlgebraicGeometry.Scheme.PreRelation
