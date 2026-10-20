module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.Topology.KrullDimension.Local
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension

/-!
# Relative dimension of morphisms of algebraic spaces

A morphism of algebraic spaces has relative dimension at most `d`, or equal to
`d`, when the local topological Krull dimension of an étale-local
scheme-theoretic fibre is bounded by, or equal to, `d` at every point of the
source.
-/

@[expose] public section

open CategoryTheory

universe u

#check (AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → ℕ → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.relativeDimensionLE_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ),
    AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLE f d ↔
      ∀ x : AlgebraicGeometry.AlgebraicSpace.Points X,
        AlgebraicGeometry.AlgebraicSpace.RelativeDimensionLEAt f d x)

#check (AlgebraicGeometry.AlgebraicSpace.RelativeDimension :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S},
    (X ⟶ Y) → ℕ → Prop)
#check (AlgebraicGeometry.AlgebraicSpace.relativeDimension_iff :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ),
    AlgebraicGeometry.AlgebraicSpace.RelativeDimension f d ↔
      ∀ x : AlgebraicGeometry.AlgebraicSpace.Points X,
        AlgebraicGeometry.AlgebraicSpace.RelativeDimensionAt f d x)
