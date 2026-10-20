/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Restriction
public import ReasLib.AlgebraicGeometry.FormalDeformation.Scheme.TwoAffineOpenCover
public import ReasLib.AlgebraicGeometry.FormalDeformation.Smooth
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Pair
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Cofibered

/-!
# Pairing of open restrictions of scheme deformations

The product `Def_{U₁} ×_{C_Λ} Def_{U₂}` of the deformation categories of the
two affine opens, and the pairing of the two restriction functors from `Def_X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open scoped AlgebraicGeometry BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {X : Scheme.{u}} (c : TwoAffineOpenCover X)
variable (hX : X ⟶ Spec (CommRingCat.of (ArtinianLocalAlgCat.residue Λ k).carrier))
variable [AlgebraicGeometry.Flat hX]

/-- The based category `Def_X` over `ArtinianLocalAlgCat`. -/
abbrev deformationBased :=
  BasedCategory.ofFunctor
    (Over.forget (Fiber.fiberInclusion.obj (FlatSchemeCat.residueObj Λ k X hX)) ⋙
      FlatSchemeCat.forget Λ k)

/-- The based category `Def_{U₁}` over `ArtinianLocalAlgCat`. -/
abbrev deformationBased_U₁ :=
  BasedCategory.ofFunctor
    (Over.forget (Fiber.fiberInclusion.obj
        (FlatSchemeCat.residueObj Λ k c.U₁.toScheme (structureHom₁ Λ k c hX))) ⋙
      FlatSchemeCat.forget Λ k)

/-- The based category `Def_{U₂}` over `ArtinianLocalAlgCat`. -/
abbrev deformationBased_U₂ :=
  BasedCategory.ofFunctor
    (Over.forget (Fiber.fiberInclusion.obj
        (FlatSchemeCat.residueObj Λ k c.U₂.toScheme (structureHom₂ Λ k c hX))) ⋙
      FlatSchemeCat.forget Λ k)

/-- The product `Def_{U₁} ×_{C_Λ} Def_{U₂}` of deformation categories over
`ArtinianLocalAlgCat`. -/
abbrev openProduct :=
  BasedCategory.PseudoPullback
    (BasedCategory.toBase (deformationBased_U₁ Λ k c hX))
    (BasedCategory.toBase (deformationBased_U₂ Λ k c hX))

/-- The pairing `Def_X ⥤ᵇ Def_{U₁} ×_{C_Λ} Def_{U₂}` of the two open restriction
functors. -/
def toOpenProduct : deformationBased Λ k hX ⥤ᵇ openProduct Λ k c hX :=
  BasedCategory.PseudoPullback.pair
    (FlatSchemeCat.restrictOpen Λ k X hX c.U₁)
    (FlatSchemeCat.restrictOpen Λ k X hX c.U₂)

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
