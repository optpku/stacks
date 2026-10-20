/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.PseudoPullback
public import ReasLib.CategoryTheory.Cofibered.InGroupoids

/-!
# Two-fibre products of deformation categories

Predeformation categories and deformation categories are closed under the
concrete two-fibre product of categories cofibered in groupoids.
-/

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

attribute [instance] IsDeformationCategory.hasRimSchlessinger

/-- The 2-fibre product of predeformation categories is a predeformation category. Its residue
fibre is nonempty with a unique morphism between any two objects. -/
instance instIsPredeformationCategory_twoFibreProduct
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [IsPredeformationCategory F.p] [IsPredeformationCategory G.p] [IsPredeformationCategory H.p] :
    IsPredeformationCategory (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) := sorry

/-- The two-fibre product of a cospan of deformation categories is a deformation category. -/
instance instIsDeformationCategory_twoFibreProduct
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p] :
    IsDeformationCategory (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) where
  toIsPredeformationCategory := instIsPredeformationCategory_twoFibreProduct f g
  hasRimSchlessinger := instHasRimSchlessingerPseudoPullback f.hom g.hom

end CategoryTheory.Functor
