module

public import ReasLib.AlgebraicGeometry.FormalDeformation.AlgebraicSpace.Deformation
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory.Over

/-!
# Rim-Schlessinger condition for algebraic spaces

The projection from flat algebraic spaces over Artinian local algebras to their
base algebras satisfies the Rim-Schlessinger condition. Its residue-object
slices are deformation categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Functor

noncomputable section

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatAlgebraicSpaceCat

/-- The projection from deformations of an algebraic space over the residue field
to their Artinian local base algebras. -/
abbrev deformationForget (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    deformation Λ k X ⥤ ArtinianLocalAlgCat Λ k :=
  Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X)) ⋙ forget Λ k

/-- The deformation projection is the slice-forgetful functor followed by the
projection to the base algebra. -/
theorem deformationForget_eq (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    deformationForget Λ k X =
      Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X)) ⋙ forget Λ k := rfl

/-- The projection from flat algebraic spaces over Artinian local algebras to
their base algebras satisfies the Rim-Schlessinger condition. -/
instance instHasRimSchlessinger_forget : HasRimSchlessinger (forget Λ k) := sorry

/-- The residue-object slice associated to any algebraic space over the residue
field is a deformation category under its projection to the base algebra. -/
instance instIsDeformationCategory_deformationForget
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    IsDeformationCategory (deformationForget Λ k X) :=
  instIsDeformationCategory_overForget (forget Λ k) (residueObj Λ k X)

end FlatAlgebraicSpaceCat
