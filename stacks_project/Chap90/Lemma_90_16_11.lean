module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Remark_90_6_4

/-!
# Localizing the Rim-Schlessinger condition at a residue-fibre object

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (RS),
then so does its slice at any residue-fibre object, and that slice is a deformation
category.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.16.11 (1): if `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies (RS) and
`x` is an object of the residue fibre `p.Fiber (ArtinianLocalAlgCat.residue Λ k)`,
then the slice `Over.forget (Fiber.fiberInclusion.obj x) ⋙ p` of Remark 90.6.4
also satisfies (RS). -/
@[stacks 06JC]
instance instHasRimSchlessinger_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    HasRimSchlessinger (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

/-- Lemma 90.16.11 (2): in particular, the slice
`Over.forget (Fiber.fiberInclusion.obj x) ⋙ p` is a deformation category. -/
@[stacks 06JC]
instance instIsDeformationCategory_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    IsDeformationCategory (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

end CategoryTheory.Functor
