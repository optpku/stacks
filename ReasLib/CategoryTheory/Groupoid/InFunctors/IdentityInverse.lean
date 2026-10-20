/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Groupoid.InFunctors

/-!
# Identity and inverse morphisms of a groupoid in functors

Identity and inverse natural transformations are characterized by the groupoid
laws on generalized arrows and are uniquely determined by those laws.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.GroupoidInFunctors

variable {C : Type u} [Category.{v} C]

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

/-- An identity natural transformation is precisely the specified identity map. -/
theorem isIdentity_iff (G : GroupoidInFunctors C) (e' : G.U ⟶ G.R) :
    IsIdentity G e' ↔ e' = G.e := sorry

/-- An inverse natural transformation is precisely the specified inverse map. -/
theorem isInverse_iff (G : GroupoidInFunctors C) (i' : G.R ⟶ G.R) :
    IsInverse G i' ↔ i' = G.i := sorry

end CategoryTheory.GroupoidInFunctors
