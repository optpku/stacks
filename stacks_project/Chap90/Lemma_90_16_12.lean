module

public import stacks_project.Chap90.Definition_90_16_8_RimSchlessinger
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids

/-!
# 2-fibre products of Rim-Schlessinger categories

The Rim-Schlessinger condition (RS) is stable under 2-fibre products of
categories cofibered in groupoids over `ArtinianLocalAlgCat Λ k`.
-/

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- Lemma 90.16.12: if `f : H ⟶ F` and `g : G ⟶ F` are morphisms of categories
cofibered in groupoids over `ArtinianLocalAlgCat Λ k` and `F`, `G`, `H` all satisfy
(RS), then the 2-fibre product `TwoFibreProduct.apex f g` satisfies (RS). -/
@[stacks 06L4]
instance instHasRimSchlessinger_twoFibreProduct
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [HasRimSchlessinger F.p] [HasRimSchlessinger G.p] [HasRimSchlessinger H.p] :
    HasRimSchlessinger (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) := sorry

end CategoryTheory.Functor
