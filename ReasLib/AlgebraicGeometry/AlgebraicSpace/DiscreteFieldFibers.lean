module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Discrete field fibers of morphisms of algebraic spaces

A morphism has discrete field fibers when every scheme-theoretic fiber over
a field-valued point has discrete space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- A morphism of algebraic spaces over `S` has discrete field fibers if for
every field `k` and every morphism `g : Spec(k) ⟶ Y` over `S`, the space of
points of the fiber product `pullback f g` is discrete. -/
def discreteFieldFibers : Prop :=
  ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y),
    DiscreteTopology (Points (pullback f g))

/-- A morphism has discrete field fibers if and only if every scheme-theoretic
field fiber `pullback f g` has discrete space of points. -/
theorem discreteFieldFibers_iff :
    discreteFieldFibers f ↔
      ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S)
        (g : ofOver (Over.mk σ) ⟶ Y),
        DiscreteTopology (Points (pullback f g)) :=
  Iff.rfl

namespace discreteFieldFibers

/-- The pointwise discreteness condition on scheme-theoretic field fibers
implies `discreteFieldFibers`. -/
theorem of
    (h : ∀ (k : Type u) [Field k] (σ : Spec (.of k) ⟶ S)
      (g : ofOver (Over.mk σ) ⟶ Y),
      DiscreteTopology (Points (pullback f g))) :
    discreteFieldFibers f :=
  h

/-- A morphism with discrete field fibers has discrete space of points on
`pullback f g` for every field-valued morphism `g : Spec(k) ⟶ Y`. -/
theorem spec (h : discreteFieldFibers f) (k : Type u) [Field k]
    (σ : Spec (.of k) ⟶ S) (g : ofOver (Over.mk σ) ⟶ Y) :
    DiscreteTopology (Points (pullback f g)) :=
  h k σ g

/-- Discreteness of field fibers is independent of the chosen fiber product:
any `IsPullback` square for `Spec(k) ×_Y X` has discrete space of points. -/
theorem of_isPullback {Xk : AlgebraicSpace S} {k : Type u} [Field k]
    {σ : Spec (.of k) ⟶ S} {g : ofOver (Over.mk σ) ⟶ Y}
    {fst : Xk ⟶ ofOver (Over.mk σ)} {snd : Xk ⟶ X}
    (h : discreteFieldFibers f) (sq : IsPullback fst snd g f) :
    DiscreteTopology (Points Xk) :=
  sorry

end discreteFieldFibers

end AlgebraicGeometry.AlgebraicSpace
