module

public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Cover.Fppf

/-!
# Fppf coverings of algebraic spaces

An fppf covering of an algebraic space is a family of morphisms that are each
flat and locally of finite presentation, and jointly surjective on points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u v

#check (AlgebraicGeometry.AlgebraicSpace.FppfCovering :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {X : AlgebraicGeometry.AlgebraicSpace S} (Xi : ι → AlgebraicGeometry.AlgebraicSpace S),
    (∀ i, Xi i ⟶ X) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.FppfCover.{u, v} :
  ∀ {S : AlgebraicGeometry.Scheme.{u}},
    AlgebraicGeometry.AlgebraicSpace S → Type (max (u + 1) (v + 1)))

#check (AlgebraicGeometry.AlgebraicSpace.FppfCovering.source_spec :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    {X : AlgebraicGeometry.AlgebraicSpace S} (Xi : ι → AlgebraicGeometry.AlgebraicSpace S)
    (f : ∀ i, Xi i ⟶ X) [AlgebraicGeometry.AlgebraicSpace.FppfCovering Xi f],
    (∀ i, AlgebraicGeometry.AlgebraicSpace.Flat (f i)) ∧
      (∀ i, AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation (f i)) ∧
        ⋃ i, Set.range (AlgebraicGeometry.AlgebraicSpace.Points.map (f i)) = Set.univ)
