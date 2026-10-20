module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over

/-!
# Rim-Schlessinger condition for flat algebras

The projection of flat commutative algebras to their Artinian local bases satisfies
the Rim-Schlessinger condition, and its residue-fibre slices are deformation categories.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraCat

/-- The projection of flat commutative algebras to their Artinian local bases
satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_forget :
    HasRimSchlessinger (forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k) := sorry

/-- The residue-fibre slice at any commutative residue-field algebra is a
deformation category under its projection to Artinian local bases. -/
instance instIsDeformationCategory_deformationCategory
    (P : Type u) [CommRing P] [Algebra k P] :
    IsDeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k P)) ⋙ forget) :=
  CategoryTheory.Functor.instIsDeformationCategory_overForget forget (residueObj Λ k P)

end FlatAlgebraCat
