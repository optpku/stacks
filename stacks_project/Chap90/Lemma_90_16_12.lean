module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.PseudoPullback
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

/-- The Rim-Schlessinger condition on the based pseudo-pullback supplies the same
condition on the two-fibre-product apex in the cofibered-category vocabulary. -/
instance instHasRimSchlessingerTwoFibreProduct
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [HasRimSchlessinger F.p] [HasRimSchlessinger G.p] [HasRimSchlessinger H.p] :
    HasRimSchlessinger (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) :=
  CategoryTheory.Functor.instHasRimSchlessingerPseudoPullback f.hom g.hom

variable
  {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
  (f : H ⟶ F) (g : G ⟶ F)
  [HasRimSchlessinger F.p] [HasRimSchlessinger G.p] [HasRimSchlessinger H.p]

/- Lemma 90.16.12: the two-fibre product of three categories cofibered in groupoids
over `ArtinianLocalAlgCat Λ k` satisfying (RS) again satisfies (RS). -/
@[stacks 06L4] #check
  (CategoryTheory.Functor.instHasRimSchlessingerPseudoPullback f.hom g.hom :
    HasRimSchlessinger (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)))

end CategoryTheory.Functor
