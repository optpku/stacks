module

public import ReasLib.AlgebraicGeometry.FormalDeformation.GradedAlgebra
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over

/-!
# Rim-Schlessinger condition for finite projective graded algebras

The projection of finite projective graded algebras satisfies the Rim-Schlessinger
condition, and its residue-fibre slices are deformation categories.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FiniteProjectiveGradedAlgebraCat

/-- The projection of commutative graded algebras with finite projective homogeneous
pieces to their Artinian local bases satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_forget :
    HasRimSchlessinger (forget : FiniteProjectiveGradedAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) :=
  sorry

/-- The residue-fibre slice at a graded algebra with finite-dimensional homogeneous
pieces is a deformation category under its projection to Artinian local bases. -/
instance instIsDeformationCategory_deformationCategory (P : FiniteProjectiveGradedAlgebra k) :
    IsDeformationCategory (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ P)) ⋙ forget) :=
  CategoryTheory.Functor.instIsDeformationCategory_overForget forget (residueObj Λ P)

end FiniteProjectiveGradedAlgebraCat
