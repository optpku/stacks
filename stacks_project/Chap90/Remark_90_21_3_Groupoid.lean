module

public import stacks_project.Chap90.Definition_90_21_1_Groupoid

/-!
# Identity and inverse morphisms of a groupoid in functors

This module records the identity and inverse morphisms of functors associated
to a groupoid in functors on a category, as unique maps sending objects to
identity arrows and arrows to inverse arrows in each fibre.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

/-- The identity arrow on an object of the fibre at `T`. -/
def idArrow (G : GroupoidInFunctors.{u, v, w} C) {T : C} (x : G.U.obj T) : G.R.obj T :=
  G.e.app T x

/-- The identity arrow on `x` has source `x`. -/
theorem idArrow_source (G : GroupoidInFunctors.{u, v, w} C) {T : C} (x : G.U.obj T) :
    G.s.app T (G.idArrow x) = x := sorry

/-- The identity arrow on `x` has target `x`. -/
theorem idArrow_target (G : GroupoidInFunctors.{u, v, w} C) {T : C} (x : G.U.obj T) :
    G.t.app T (G.idArrow x) = x := sorry

/-- The inverse of an arrow of the fibre at `T`. -/
def invArrow (G : GroupoidInFunctors.{u, v, w} C) {T : C} (a : G.R.obj T) : G.R.obj T :=
  G.i.app T a

/-- The inverse of `a` has source equal to the target of `a`. -/
theorem invArrow_source (G : GroupoidInFunctors.{u, v, w} C) {T : C} (a : G.R.obj T) :
    G.s.app T (G.invArrow a) = G.t.app T a := sorry

/-- The inverse of `a` has target equal to the source of `a`. -/
theorem invArrow_target (G : GroupoidInFunctors.{u, v, w} C) {T : C} (a : G.R.obj T) :
    G.t.app T (G.invArrow a) = G.s.app T a := sorry

/-- `G.idArrow x` is the identity morphism on `x` in the fibre groupoid at `T`. -/
theorem idArrow_spec (G : GroupoidInFunctors.{u, v, w} C) {T : C} (x : G.U.obj T) :
    ((G.pointGroupoid T).id x).arrow = G.idArrow x := sorry

/-- `G.invArrow p.arrow` is the inverse of `p` in the fibre groupoid at `T`. -/
theorem invArrow_spec (G : GroupoidInFunctors.{u, v, w} C) {T : C} {x y : G.U.obj T}
    (p : G.PointHom T x y) :
    ((G.pointGroupoid T).inv p).arrow = G.invArrow p.arrow := sorry

/-- A morphism of functors `e' : G.U ⟶ G.R` is an identity if it sends each object
to an identity arrow of the fibre groupoid determined by `G.s`, `G.t`, and `G.c`. -/
def IsIdentity (G : GroupoidInFunctors C) (e' : G.U ⟶ G.R) : Prop :=
  e' ≫ G.s = 𝟙 G.U ∧
    e' ≫ G.t = 𝟙 G.U ∧
      (∀ {W : C ⥤ Type w} (a : W ⟶ G.R)
          (h : a ≫ G.s = ((a ≫ G.s) ≫ e') ≫ G.t),
          G.compose a ((a ≫ G.s) ≫ e') h = a) ∧
        ∀ {W : C ⥤ Type w} (a : W ⟶ G.R)
          (h : ((a ≫ G.t) ≫ e') ≫ G.s = a ≫ G.t),
          G.compose ((a ≫ G.t) ≫ e') a h = a

/-- A morphism of functors `i' : G.R ⟶ G.R` is an inverse if it sends each arrow
to an inverse arrow of the fibre groupoid determined by `G.s`, `G.t`, and `G.c`. -/
def IsInverse (G : GroupoidInFunctors C) (i' : G.R ⟶ G.R) : Prop :=
  i' ≫ G.s = G.t ∧
    i' ≫ G.t = G.s ∧
      (∀ {W : C ⥤ Type w} (a : W ⟶ G.R)
          (h : a ≫ G.s = (a ≫ i') ≫ G.t),
          G.compose a (a ≫ i') h = (a ≫ G.t) ≫ G.e) ∧
        ∀ {W : C ⥤ Type w} (a : W ⟶ G.R)
          (h : (a ≫ i') ≫ G.s = a ≫ G.t),
          G.compose (a ≫ i') a h = (a ≫ G.s) ≫ G.e

/-- The packaged identity map is an identity morphism of functors. -/
theorem isIdentity_e (G : GroupoidInFunctors C) : IsIdentity G G.e := sorry

/-- The packaged inverse map is an inverse morphism of functors. -/
theorem isInverse_i (G : GroupoidInFunctors C) : IsInverse G G.i := sorry

/-- An identity morphism of functors sends `x ∈ G.U.obj T` to an arrow with source `x`. -/
theorem isIdentity_app_source (G : GroupoidInFunctors.{u, v, w} C) {e' : G.U ⟶ G.R}
    (h : IsIdentity G e') (T : C) (x : G.U.obj T) :
    G.s.app T (e'.app T x) = x := sorry

/-- An identity morphism of functors sends `x ∈ G.U.obj T` to an arrow with target `x`. -/
theorem isIdentity_app_target (G : GroupoidInFunctors.{u, v, w} C) {e' : G.U ⟶ G.R}
    (h : IsIdentity G e') (T : C) (x : G.U.obj T) :
    G.t.app T (e'.app T x) = x := sorry

/-- An inverse morphism of functors sends `a ∈ G.R.obj T` to an arrow whose source is
the target of `a`. -/
theorem isInverse_app_source (G : GroupoidInFunctors.{u, v, w} C) {i' : G.R ⟶ G.R}
    (h : IsInverse G i') (T : C) (a : G.R.obj T) :
    G.s.app T (i'.app T a) = G.t.app T a := sorry

/-- An inverse morphism of functors sends `a ∈ G.R.obj T` to an arrow whose target is
the source of `a`. -/
theorem isInverse_app_target (G : GroupoidInFunctors.{u, v, w} C) {i' : G.R ⟶ G.R}
    (h : IsInverse G i') (T : C) (a : G.R.obj T) :
    G.t.app T (i'.app T a) = G.s.app T a := sorry

end CategoryTheory.GroupoidInFunctors
