module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Pullback.Over
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Morphism.QuasiCompact

/-!
# Affine finite-presentation approximation of closed subsets of stack fibre products

A closed subset avoiding a base point admits an affine finite-presentation
approximation after restriction to an affine open neighbourhood of that point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- For a quasi-compact morphism from a quasi-compact algebraic stack to an affine
scheme, a closed subset of an affine base change avoiding a base point admits an
affine finite-presentation approximation on an affine open neighbourhood. The
approximating closed subset avoids the image of the chosen point and contains
the image of the inverse image of the original subset under the canonical
base-change morphisms. -/
theorem existsAffineOpenApproximationAvoidingImage
    {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X] [IsQuasiCompact X]
    {Y Z : Over S} [IsAffine Y.left] [IsAffine Z.left]
    (f : X ⟶ GroupoidsOver.slice Y) [QuasiCompact f] (g : Z ⟶ Y)
    (z : Z.left) (T : Set (Points (pullbackAlongOver f g)))
    (hT : IsClosed T)
    (hz : Points.ofSlice z ∉ Points.map (pullbackAlongOver.snd f g) '' T) :
    ∃ (V : Z.left.Opens) (hVz : z ∈ (V : Set Z.left)) (_ : IsAffine V.toScheme)
      (Z' : Over S) (_ : IsAffine Z'.left)
      (a : Over.mk (V.ι ≫ Z.hom) ⟶ Z') (b : Z' ⟶ Y)
      (_ : LocallyOfFinitePresentation b.left)
      (hcomm : a ≫ b = (Over.homMk V.ι rfl) ≫ g)
      (T' : Set (Points (pullbackAlongOver f b))) (_ : IsClosed T'),
      Points.ofSlice (a.left ⟨z, hVz⟩) ∉
          Points.map (pullbackAlongOver.snd f b) '' T' ∧
        Points.map (pullbackAlongOver.map f
          ((Over.homMk V.ι rfl : Over.mk (V.ι ≫ Z.hom) ⟶ Z) ≫ g) b a hcomm) ''
          (Points.map (pullbackAlongOver.map f
            ((Over.homMk V.ι rfl : Over.mk (V.ι ≫ Z.hom) ⟶ Z) ≫ g) g
            (Over.homMk V.ι rfl) rfl) ⁻¹' T) ⊆ T' :=
  sorry

end AlgebraicGeometry.AlgebraicStack
