module

public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Lemma_90_25_2_Pullback
public import stacks_project.Chap90.Remark_90_10_3
public import stacks_project.Chap90.Remark_90_16_9_DeformationFunctor

/-!
# Predeformation and (H2) instances for a kernel-pair deformation functor

The kernel-pair functor `relation f` of a morphism from a deformation functor to a
deformation category is a predeformation functor, and both `U` and `relation f`
satisfy Schlessinger's (H2).
-/

@[expose] public section

noncomputable section

open CategoryTheory ArtinianLocalAlgCat Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {U : ArtinianLocalAlgCat Λ k ⥤ Type (max u v)}
variable {F : CofiberedCategoryOver.Groupoids.{u + 1, u, max (u + 1) (max u v), u}
    (ArtinianLocalAlgCat Λ k)}

namespace CategoryTheory.Functor

/-- A deformation functor satisfies Schlessinger's condition (H2). -/
instance instHasSchlessingerH2_of_isDeformationFunctor
    {G : ArtinianLocalAlgCat Λ k ⥤ Type w} [IsDeformationFunctor G] :
    HasSchlessingerH2 G := sorry

/-- The category of elements of a predeformation functor is a predeformation category. -/
instance instIsPredeformationCategory_ofTypeValued
    {G : ArtinianLocalAlgCat Λ k ⥤ Type w} [IsPredeformationFunctor G] :
    IsPredeformationCategory (CategoryOfElements.π G) := sorry

end CategoryTheory.Functor

namespace CategoryTheory.GroupoidInFunctors

/-- The kernel-pair functor `relation f` of a morphism from a deformation functor to a
deformation category is a predeformation functor. -/
instance instIsPredeformationFunctor_relation (f : Functor.ofTypeValued U ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationFunctor U] :
    IsPredeformationFunctor (relation f) := sorry

/-- The kernel-pair functor `relation f` takes a unique value at the residue field. -/
theorem isPredeformationFunctor_relation_spec (f : Functor.ofTypeValued U ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationFunctor U] :
    Nonempty (Unique ((relation f).obj (residue Λ k))) := sorry

/-- The kernel-pair functor `relation f` satisfies Schlessinger's condition (H2). -/
instance instHasSchlessingerH2_relation (f : Functor.ofTypeValued U ⟶ F)
    [IsDeformationCategory F.p] [IsDeformationFunctor U] :
    HasSchlessingerH2 (relation f) := sorry

end CategoryTheory.GroupoidInFunctors
