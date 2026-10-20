module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineSpace
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support

/-!
# Dense open immersions into relative affine space

A finite-presentation morphism to a Noetherian algebraic space admits a dense open
subspace of its source that immerses into relative affine space over its target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A finite-presentation morphism to a Noetherian algebraic space admits a dense open
subspace of its source with an immersion into a finite-dimensional relative affine space
over the target, compatible with the given morphism. -/
theorem exists_dense_open_immersion_to_affineSpace {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : Y ⟶ X) [IsNoetherian X] [FinitePresentation f] :
    ∃ (V : OpenSubspace Y) (n : ℕ) (i : V.X ⟶ AffineSpace (ULift.{u} (Fin n)) X),
      Dense (V.pointsSet : Set (Points Y)) ∧ IsImmersion i ∧
        i ≫ AffineSpace.toBase (ULift.{u} (Fin n)) X = V.ι ≫ f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
