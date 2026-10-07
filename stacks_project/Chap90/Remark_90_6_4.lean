module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import stacks_project.Chap90.Definition_90_16_8_Predeformation

/-!
# Localizing a category cofibered in groupoids at a residue-fibre object

Slicing a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` at an
object of the residue fibre yields a predeformation category.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Remark 90.6.4: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids
and `x` is an object of the residue fibre `p.Fiber (ArtinianLocalAlgCat.residue Λ k)`,
the slice `F_x` of arrows `y ⟶ Fiber.fiberInclusion.obj x` (with commutative
triangles as morphisms) is `Over (Fiber.fiberInclusion.obj x)`. The forgetful
functor `F_x ⟶ F` is `Over.forget`, and
`p_x := Over.forget (Fiber.fiberInclusion.obj x) ⋙ p` is a predeformation
category. This localizes an arbitrary category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k` at any residue-fibre object. -/
@[stacks 06GU]
instance instIsPredeformationCategory_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    IsPredeformationCategory (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

end CategoryTheory.Functor
