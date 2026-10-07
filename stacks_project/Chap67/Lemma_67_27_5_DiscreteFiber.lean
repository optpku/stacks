module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Discrete field fibers of morphisms of algebraic spaces

A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` has discrete
field fibers when, for every field `k` and every morphism `Spec(k) ⟶ Y`, the
space of points of the fibre product `X ×_Y Spec(k)` is discrete.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A morphism of algebraic spaces over `S` has discrete field fibers if for
every field `k` and every morphism `g : Spec(k) ⟶ Y` over `S`, the space of
points of the chosen fibre product `pullback f g` is discrete. -/
def discreteFieldFibers : Prop :=
  ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y)
    [HasPullback f g], DiscreteTopology (Points (pullback f g))

/-- A morphism has discrete field fibers if and only if every scheme-theoretic
field fiber `pullback f g` has discrete space of points. -/
theorem discreteFieldFibers_iff :
    discreteFieldFibers f ↔
      ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S)
        (g : ofOver (Over.mk σ) ⟶ Y) [HasPullback f g],
        DiscreteTopology (Points (pullback f g)) :=
  sorry

namespace discreteFieldFibers

/-- The pointwise discreteness condition on scheme-theoretic field fibers
implies `discreteFieldFibers`. -/
theorem of
    (h : ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S)
      (g : ofOver (Over.mk σ) ⟶ Y) [HasPullback f g],
      DiscreteTopology (Points (pullback f g))) :
    discreteFieldFibers f :=
  sorry

/-- `discreteFieldFibers` implies that the chosen fibre product
`pullback f g` has discrete space of points, for every field-valued morphism
`g : Spec(k) ⟶ Y`. -/
theorem spec (h : discreteFieldFibers f) (k : Type u) [Field k]
    (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y) [HasPullback f g] :
    DiscreteTopology (Points (pullback f g)) :=
  sorry

/-- Discreteness of field fibers is independent of the chosen fibre product:
any `IsPullback` square for `Spec(k) ×_Y X` has discrete space of points. -/
theorem of_isPullback {Xk : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} {g : ofOver (Over.mk σ) ⟶ Y}
    {fst : Xk ⟶ ofOver (Over.mk σ)} {snd : Xk ⟶ X}
    (h : discreteFieldFibers f) (sq : IsPullback fst snd g f) :
    DiscreteTopology (Points Xk) :=
  sorry

end discreteFieldFibers

end AlgebraicGeometry.AlgebraicSpace
