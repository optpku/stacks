module

public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_16_12
public import stacks_project.Chap90.Remarks_90_5_2_Groupoids

/-!
# Predeformation structure on 2-fibre products

The 2-fibre product of deformation categories over `ArtinianLocalAlgCat Λ k` is again a
predeformation category: its residue fibre is the categorical pullback of two pointlike
setoids over a pointlike setoid.
-/

@[expose] public section

open CategoryTheory CofiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace CategoryTheory.Functor

/-- The 2-fibre product of deformation categories is a predeformation category. Its residue
fibre is nonempty with a unique morphism between any two objects. -/
instance instIsPredeformationCategory_twoFibreProduct
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p] :
    IsPredeformationCategory (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)) := sorry

/-- The residue fibre of `TwoFibreProduct.apex f g` is nonempty and has a unique morphism
between any two objects, as the categorical pullback of the residue fibres of `H` and `G`
over the residue fibre of `F`. -/
theorem isPredeformationCategory_twoFibreProduct_spec
    {F G H : CofiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (ArtinianLocalAlgCat Λ k)}
    (f : H ⟶ F) (g : G ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationCategory G.p] [IsDeformationCategory H.p] :
    Nonempty ((p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)).Fiber
        (ArtinianLocalAlgCat.residue Λ k)) ∧
      ∀ x y : (p (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)).Fiber
          (ArtinianLocalAlgCat.residue Λ k),
        Nonempty (x ⟶ y) ∧ Subsingleton (x ⟶ y) := sorry

end CategoryTheory.Functor
