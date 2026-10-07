module

public import stacks_project.Chap66.Lemma_66_18_3_Site

/-!
# Commutative squares of étale schemes over a morphism of algebraic spaces

An object of the small étale site of an algebraic space is a scheme étale over that space. An
`f`-square records a morphism of schemes `g : U ⟶ V` making the evident square over `f` commute.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A commutative square of schemes étale over a morphism `f : X ⟶ Y` of algebraic spaces: the
left edge is an object of `smallEtaleSite X`, the right edge is an object of `smallEtaleSite Y`,
and `map` is a morphism of schemes over `S` making the square commute. -/
structure EtaleSquare {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) where
  /-- The object `U` of the small étale site of `X`. -/
  left : smallEtaleSite X
  /-- The object `V` of the small étale site of `Y`. -/
  right : smallEtaleSite Y
  /-- The morphism of schemes over `S` from `U` to `V`. -/
  map : left.left ⟶ right.left
  /-- The square `U ⟶ X`, `V ⟶ Y`, `U ⟶ V` commutes with `f`. -/
  w : left.hom ≫ f = ofOverMap map ≫ right.hom

namespace EtaleSquare

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}

/-- Reconstruct an `f`-square from a pair of étale scheme objects and a commuting morphism of
schemes over `S`. -/
def ofSchemeMap (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
    (w : U.hom ≫ f = ofOverMap g ≫ V.hom) : EtaleSquare f where
  left := U
  right := V
  map := g
  w := w

/-- The left object of `ofSchemeMap U V g w` is `U`. -/
@[simp]
theorem ofSchemeMap_left (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
    (w : U.hom ≫ f = ofOverMap g ≫ V.hom) : (ofSchemeMap U V g w).left = U :=
  sorry

/-- The right object of `ofSchemeMap U V g w` is `V`. -/
@[simp]
theorem ofSchemeMap_right (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
    (w : U.hom ≫ f = ofOverMap g ≫ V.hom) : (ofSchemeMap U V g w).right = V :=
  sorry

/-- The underlying scheme morphism of `ofSchemeMap U V g w` is `g`. -/
@[simp]
theorem ofSchemeMap_map (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
    (w : U.hom ≫ f = ofOverMap g ≫ V.hom) : (ofSchemeMap U V g w).map = g :=
  sorry

/-- `ofSchemeMap U V g w` recovers the source square with vertices `U`, `V` and edge `g`. -/
theorem ofSchemeMap_spec (U : smallEtaleSite X) (V : smallEtaleSite Y) (g : U.left ⟶ V.left)
    (w : U.hom ≫ f = ofOverMap g ≫ V.hom) :
    (ofSchemeMap U V g w).left = U ∧ (ofSchemeMap U V g w).right = V ∧
      (ofSchemeMap U V g w).map = g ∧
        (ofSchemeMap U V g w).left.hom ≫ f =
          ofOverMap (ofSchemeMap U V g w).map ≫ (ofSchemeMap U V g w).right.hom :=
  sorry

/-- The restricted square over `f` obtained from an extended étale diagram still commutes. -/
theorem restrict_w {U' : smallEtaleSite X} {V' : smallEtaleSite Y} (sq : EtaleSquare f)
    (i : U' ⟶ sq.left) (j : V' ⟶ sq.right) (g' : U'.left ⟶ V'.left)
    (hij : i.left ≫ sq.map = g' ≫ j.left) :
    U'.hom ≫ f = ofOverMap g' ≫ V'.hom :=
  sorry

/-- The `f`-square obtained by restricting along morphisms `U' ⟶ U` and `V' ⟶ V` in the small
étale sites, using a compatible scheme morphism `g' : U' ⟶ V'`. -/
def restrict {U' : smallEtaleSite X} {V' : smallEtaleSite Y} (sq : EtaleSquare f)
    (i : U' ⟶ sq.left) (j : V' ⟶ sq.right) (g' : U'.left ⟶ V'.left)
    (hij : i.left ≫ sq.map = g' ≫ j.left) : EtaleSquare f :=
  ofSchemeMap U' V' g' (restrict_w sq i j g' hij)

/-- The left object of a restricted square is the source of the restriction morphism into `U`. -/
@[simp]
theorem restrict_left {U' : smallEtaleSite X} {V' : smallEtaleSite Y} (sq : EtaleSquare f)
    (i : U' ⟶ sq.left) (j : V' ⟶ sq.right) (g' : U'.left ⟶ V'.left)
    (hij : i.left ≫ sq.map = g' ≫ j.left) : (sq.restrict i j g' hij).left = U' :=
  sorry

/-- The right object of a restricted square is the source of the restriction morphism into `V`. -/
@[simp]
theorem restrict_right {U' : smallEtaleSite X} {V' : smallEtaleSite Y} (sq : EtaleSquare f)
    (i : U' ⟶ sq.left) (j : V' ⟶ sq.right) (g' : U'.left ⟶ V'.left)
    (hij : i.left ≫ sq.map = g' ≫ j.left) : (sq.restrict i j g' hij).right = V' :=
  sorry

/-- The scheme morphism of a restricted square is the given compatible map `g'`. -/
@[simp]
theorem restrict_map {U' : smallEtaleSite X} {V' : smallEtaleSite Y} (sq : EtaleSquare f)
    (i : U' ⟶ sq.left) (j : V' ⟶ sq.right) (g' : U'.left ⟶ V'.left)
    (hij : i.left ≫ sq.map = g' ≫ j.left) : (sq.restrict i j g' hij).map = g' :=
  sorry

/-- For a square over the identity of `X`, the scheme morphism `U ⟶ V` is a triangle over `X`. -/
theorem homMk_w {X : AlgebraicSpace S} (sq : EtaleSquare (𝟙 X)) :
    ofOverMap sq.map ≫ sq.right.hom = sq.left.hom :=
  sorry

/-- The morphism in `smallEtaleSite X` from the left object of an identity square to the right
object, with underlying scheme map `sq.map`. -/
def homMk {X : AlgebraicSpace S} (sq : EtaleSquare (𝟙 X)) : sq.left ⟶ sq.right :=
  MorphismProperty.CostructuredArrow.homMk sq.map trivial (homMk_w sq)

/-- The underlying morphism of schemes of `homMk sq` is `sq.map`. -/
@[simp]
theorem homMk_left {X : AlgebraicSpace S} (sq : EtaleSquare (𝟙 X)) :
    (homMk sq).left = sq.map :=
  sorry

end EtaleSquare

end AlgebraicGeometry.AlgebraicSpace
