/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap90.Definition_90_8_1_Smooth
public import stacks_project.Chap90.Definition_90_12_3
public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger

/-!
# Smoothness of a map of deformation categories from a smooth composite

If `F → G → H` are morphisms of categories cofibered in groupoids over
`ArtinianLocalAlgCat Λ k`, `F` and `G` are deformation categories, the
differential `TF → TG` is surjective, and `F → H` is smooth, then `F → G` is
smooth.
-/

@[expose] public section

open CategoryTheory Functor
open scoped Bicategory

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F G H : Type v} [Category.{w} F] [Category.{w} G] [Category.{w} H]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} {q : G ⥤ ArtinianLocalAlgCat Λ k}
  {r : H ⥤ ArtinianLocalAlgCat Λ k}
variable [IsPredeformationCategory p] [HasRimSchlessinger p]
variable [IsPredeformationCategory q] [HasRimSchlessinger q]
variable [IsFibered.InGroupoids p.op] [IsFibered.InGroupoids q.op]
variable [IsFibered.InGroupoids r.op]

namespace CategoryTheory.BasedFunctor

/-- Lemma 90.20.4: let `φ : F ⥤ᵇ G` and `ψ : G ⥤ᵇ H` be morphisms of categories
cofibered in groupoids over `ArtinianLocalAlgCat Λ k`. If `F` and `G` are deformation
categories, the map `TF → TG` given by `differential φ` is surjective, and `φ ⋙ ψ`
is smooth, then `φ` is smooth. -/
@[stacks 0E3R]
theorem isSmooth_of_comp_surjective_differential
    (φ : BasedCategory.ofFunctor p ⥤ᵇ BasedCategory.ofFunctor q)
    (ψ : BasedCategory.ofFunctor q ⥤ᵇ BasedCategory.ofFunctor r)
    (hsurj : Function.Surjective (differential φ))
    (hcomp : IsSmooth (φ ⋙ ψ)) : IsSmooth φ := sorry

end CategoryTheory.BasedFunctor
