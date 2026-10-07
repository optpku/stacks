module

public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap76.Lemma_76_14_4_FormallyUnramified
public import stacks_project.Chap76.Lemma_76_18_1_Thickening

/-!
# Uniqueness of lifts for formally unramified morphisms of algebraic spaces

A formally unramified morphism of algebraic spaces over a scheme `S` admits at
most one lift through an arbitrary first-order thickening of algebraic spaces
over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.FormallyUnramified

/-- Lemma 76.14.3: If `f : X ⟶ Y` is a formally unramified morphism of algebraic
spaces over a scheme `S`, then a solid commutative square against any first-order
thickening `i : T ⟶ T'` of algebraic spaces over `S` admits at most one dotted
lift `T' ⟶ X`. -/
@[stacks 05ZY]
instance subsingleton_liftStruct {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S}
    (f : X ⟶ Y) [FormallyUnramified f] (i : T ⟶ T') [IsFirstOrderThickening i]
    (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b) :
    Subsingleton sq.LiftStruct :=
  sorry

/-- Two morphisms `T' ⟶ X` that agree after composition with a first-order
thickening `i : T ⟶ T'` and over `Y` are equal, when `X ⟶ Y` is formally
unramified. -/
theorem hom_ext {S : Scheme.{u}} {X Y T T' : AlgebraicSpace S} {f : X ⟶ Y}
    [FormallyUnramified f] {i : T ⟶ T'} [IsFirstOrderThickening i]
    {a₁ a₂ : T' ⟶ X} (hT : i ≫ a₁ = i ≫ a₂) (hY : a₁ ≫ f = a₂ ≫ f) :
    a₁ = a₂ :=
  sorry

/-- A morphism of algebraic spaces is formally unramified if and only if lifts
through an arbitrary first-order thickening of algebraic spaces are unique
whenever they exist. -/
theorem iff_subsingleton_liftStruct {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    FormallyUnramified f ↔
      ∀ {T T' : AlgebraicSpace S} (i : T ⟶ T') [IsFirstOrderThickening i]
        (a : T ⟶ X) (b : T' ⟶ Y) (sq : CommSq a i f b),
        Subsingleton sq.LiftStruct :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.FormallyUnramified
