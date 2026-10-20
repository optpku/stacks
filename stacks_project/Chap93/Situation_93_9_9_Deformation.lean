module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover

/-!
# Deformation categories of a two-chart affine cover

The shared two-chart deformation categories, together with the source-facing
abbreviation for the deformation category of the covered scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}}

/-- The deformation category of the covered scheme, retained for source compatibility. -/
abbrev deformationCategory
    (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier)) :=
  FlatSchemeCat.deformationCategory Λ k X hX

variable (c : TwoAffineOpenCover X)
  (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))

#check (FlatSchemeCat.deformationCategory_spec Λ k X hX :
  FlatSchemeCat.deformationCategory Λ k X hX =
    Over (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)))

#check (structureHom₁ Λ k c hX :
  c.U₁.toScheme ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
#check (algebraRing₁ Λ k c hX : Algebra k Γ(X, c.U₁))

#check (structureHom₂ Λ k c hX :
  c.U₂.toScheme ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
#check (algebraRing₂ Λ k c hX : Algebra k Γ(X, c.U₂))

#check (structureHomInf Λ k c hX :
  (c.U₁ ⊓ c.U₂).toScheme ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
#check (algebraRingInf Λ k c hX : Algebra k Γ(X, (c.U₁ ⊓ c.U₂)))

#check (deformationCategory_U₁ Λ k c hX : Type (u + 1))
#check (deformationCategory_U₁_spec Λ k c hX :
  deformationCategory_U₁ Λ k c hX =
    Over (Fiber.fiberInclusion.obj
      (FlatSchemeCat.residueObj Λ k c.U₁.toScheme (structureHom₁ Λ k c hX))))

#check (deformationCategory_U₂ Λ k c hX : Type (u + 1))
#check (deformationCategory_U₂_spec Λ k c hX :
  deformationCategory_U₂ Λ k c hX =
    Over (Fiber.fiberInclusion.obj
      (FlatSchemeCat.residueObj Λ k c.U₂.toScheme (structureHom₂ Λ k c hX))))

#check (deformationCategory_inf Λ k c hX : Type (u + 1))
#check (deformationCategory_inf_spec Λ k c hX :
  deformationCategory_inf Λ k c hX =
    Over (Fiber.fiberInclusion.obj
      (FlatSchemeCat.residueObj Λ k (c.U₁ ⊓ c.U₂).toScheme (structureHomInf Λ k c hX))))

#check (deformationCategory_ring₁ Λ k c hX : Type (u + 1))
#check (deformationCategory_ring₁_spec Λ k c hX :
  deformationCategory_ring₁ Λ k c hX =
    (let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₁
     Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P))))

#check (deformationCategory_ring₂ Λ k c hX : Type (u + 1))
#check (deformationCategory_ring₂_spec Λ k c hX :
  deformationCategory_ring₂ Λ k c hX =
    (let P : CommAlgCat k := hX.sectionsAlgOverSpec c.U₂
     Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P))))

#check (deformationCategory_ringInf Λ k c hX : Type (u + 1))
#check (deformationCategory_ringInf_spec Λ k c hX :
  deformationCategory_ringInf Λ k c hX =
    (let P : CommAlgCat k := hX.sectionsAlgOverSpec (c.U₁ ⊓ c.U₂)
     Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P))))

end AlgebraicGeometry.Scheme.TwoAffineOpenCover
