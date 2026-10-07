module

public import stacks_project.Chap90.Definition_90_9_1_Smooth

/-!
# Smooth or unobstructed categories cofibered in groupoids

A category cofibered in groupoids over `C_Λ` is smooth, or unobstructed, when
its structure morphism is a smooth morphism of categories cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type w} [Category.{v} F]

namespace CategoryTheory.Functor

/-- Definition 90.9.1: a category cofibered in groupoids `p : F ⥤ ArtinianLocalAlgCat Λ k`
is smooth, or unobstructed, if and only if its structure morphism
`BasedCategory.toBase (BasedCategory.ofFunctor p)` is smooth in the sense of
Definition 90.8.1. -/
@[stacks 06HP]
theorem isSmooth_iff (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    IsSmooth p ↔
      BasedFunctor.IsSmooth (BasedCategory.toBase (BasedCategory.ofFunctor p)) := sorry

end CategoryTheory.Functor
