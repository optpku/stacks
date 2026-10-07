module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.Topology.KrullDimension.Local
public import stacks_project.Chap67.Lemma_67_22_5
public import stacks_project.Chap67.Lemma_67_22_5_EtaleLocal

/-!
# Relative dimension of morphisms of algebraic spaces at a point

A morphism of algebraic spaces has relative dimension `d` at a source point
when some (equivalently, any) étale scheme square through that point has
scheme-theoretic fibre of local topological Krull dimension `d`. This is the
quantity `dim_u(U_v)` of Descent Lemma 35.33.8, tested as in Lemma 67.22.5.
The parameter `d` ranges over `ℕ∞`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces has relative dimension `d` at a
point `x` of `|X|` if some étale scheme square through `x` has scheme-theoretic
fibre of local topological Krull dimension `d` at the corresponding point of
`U`. -/
def RelativeDimensionAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left),
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.mapOfOver a u = x ∧
            topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞)

/-- Relative dimension `d` at `x` is the existence of an étale scheme square
through `x` with `dim_u(U_v) = d`. -/
theorem relativeDimensionAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) :
    RelativeDimensionAt f d x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.mapOfOver a u = x ∧
                topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

/-- Relative dimension `d` at `x` holds if and only if every étale scheme square
through `x` has `dim_u(U_v) = d`. -/
theorem relativeDimensionAt_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) :
    RelativeDimensionAt f d x ↔
      ∀ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = ofOverMap h ≫ b →
              Points.mapOfOver a u = x →
                topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

namespace RelativeDimensionAt

/-- An étale scheme square over `f` through `x` with `dim_u(U_v) = d` witnesses
`RelativeDimensionAt f d x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞}
    {x : Points X} {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x)
    (hd : topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞)) :
    RelativeDimensionAt f d x :=
  sorry

/-- If `f` has relative dimension `d` at `x`, then any étale scheme square
through `x` has `dim_u(U_v) = d`. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞}
    {x : Points X} (hf : RelativeDimensionAt f d x) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

end RelativeDimensionAt

/-- Given one étale scheme square over `f` through `x`, `f` has relative
dimension `d` at `x` if and only if `dim_u(U_v) = d`. -/
theorem relativeDimensionAt_iff_of_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞} {x : Points X}
    {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    RelativeDimensionAt f d x ↔
      topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the relative dimension at the image of `u` is `d` if and only if
`dim_u(U_v) = d`. -/
theorem relativeDimensionAt_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (d : ℕ∞) (u : U.left) :
    RelativeDimensionAt (ofOverMap h) d (ofOver.pointsEquiv U u) ↔
      topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
