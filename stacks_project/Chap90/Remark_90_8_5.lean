module

public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Remark_90_8_5_IsoClass

/-!
# Smoothness of the morphism to fibrewise isomorphism classes

If `F` is cofibered in groupoids over `ArtinianLocalAlgCat Λ k`, then the canonical
morphism to the category of fibrewise isomorphism classes is smooth.
-/

@[expose] public section

open CategoryTheory
open scoped BasedFunctor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.BasedFunctor

/-- Remark 90.8.5: if `F` is a category cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`, then the canonical morphism `toIsoClass p` from `F` to
the category of fibrewise isomorphism classes is smooth. -/
@[stacks 06HK]
instance instIsSmoothToIsoClass {F : Type w} [Category.{v} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    IsSmooth (toIsoClass p) := sorry

end CategoryTheory.BasedFunctor
