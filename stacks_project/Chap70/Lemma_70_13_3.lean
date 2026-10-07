module

public import Mathlib.Topology.Defs.Basic
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap70.Lemma_70_13_3_AffineSpace

/-!
# Embedding into affine space over a Noetherian algebraic space

A morphism of finite presentation from an algebraic space into a Noetherian algebraic
space admits a dense open on the source that immerses into a finite-dimensional relative
affine space over the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 70.13.3: Let `S` be a scheme. Let `f : Y ⟶ X` be a morphism of algebraic spaces
over `S`. Assume `X` is Noetherian and `f` is of finite presentation. Then there exists a
dense open `V ⊂ Y` and an immersion `V.X ⟶ AffineSpace (ULift (Fin n)) X` over `X`. -/
@[stacks 088N]
theorem exists_dense_open_immersion_to_affineSpace {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsNoetherian X] [FinitePresentation f] :
    ∃ (V : OpenSubspace Y) (n : ℕ) (i : V.X ⟶ AffineSpace (ULift.{u} (Fin n)) X),
      Dense (V.pointsSet : Set (Points Y)) ∧ IsImmersion i ∧
        i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = V.ι ≫ f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
