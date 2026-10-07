module

public import stacks_project.Chap90.Definition_90_10_1_Schlessinger
public import stacks_project.Chap90.Remark_90_6_4

/-!
# Localizing Schlessinger's conditions at a residue-fibre object

If a category cofibered in groupoids over `ArtinianLocalAlgCat Λ k` satisfies (S1)
or (S2), then so does its slice at any residue-fibre object.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

/-- Lemma 90.10.6 (1): if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids,
satisfies (S1), and `x` is an object of the residue fibre
`p.Fiber (ArtinianLocalAlgCat.residue Λ k)`, then the slice
`Over.forget (Fiber.fiberInclusion.obj x) ⋙ p` of Remark 90.6.4 also satisfies (S1). -/
@[stacks 06SQ]
instance instHasSchlessingerS1_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS1 p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    HasSchlessingerS1 (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

/-- Lemma 90.10.6 (2): if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids,
satisfies (S2), and `x` is an object of the residue fibre
`p.Fiber (ArtinianLocalAlgCat.residue Λ k)`, then the slice
`Over.forget (Fiber.fiberInclusion.obj x) ⋙ p` of Remark 90.6.4 also satisfies (S2). -/
@[stacks 06SQ]
instance instHasSchlessingerS2_overForget
    (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [IsFibered.InGroupoids p.op] [HasSchlessingerS2 p]
    (x : p.Fiber (ArtinianLocalAlgCat.residue Λ k)) :
    HasSchlessingerS2 (Over.forget (Fiber.fiberInclusion.obj x) ⋙ p) := sorry

end CategoryTheory.Functor
