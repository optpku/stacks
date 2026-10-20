/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import ReasLib.Algebra.Homology.Homotopy.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal functors on homotopy categories

An additive functor acts termwise on complexes and hence on their homotopy categories.  A unit
isomorphism and tensor comparison on complexes descend independently to the homotopy category;
the tensor comparison does not need to be invertible.  When the termwise functor and both quotient
functors are strong monoidal, the universal property of monoidal localization also supplies the
strong monoidal structure after passage to homotopy categories.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Homotopy

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D]
variable (F : C ⥤ D) [F.Additive]

/-- The standard factorization of the termwise action of `F` through the homotopy quotient,
packaged as the lifting datum expected by localization APIs. -/
@[stacks 07A4 "termwise functor homotopy lifting", implicit_reducible]
noncomputable instance mapLifting :
    Localization.Lifting
      (HomotopyCategory.quotient C (up ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ) :
        MorphismProperty (CochainComplex C ℤ))
      (F.mapHomologicalComplex (up ℤ) ⋙ HomotopyCategory.quotient D (up ℤ))
      (F.mapHomotopyCategory (up ℤ)) where
  iso := F.mapHomotopyCategoryFactors (up ℤ)

/-- The localization lifting isomorphism is the canonical factorization isomorphism for
`mapHomotopyCategory`. -/
@[simp]
theorem mapLifting_iso :
    Localization.Lifting.iso
      (HomotopyCategory.quotient C (up ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ) :
        MorphismProperty (CochainComplex C ℤ))
      (F.mapHomologicalComplex (up ℤ) ⋙ HomotopyCategory.quotient D (up ℤ))
      (F.mapHomotopyCategory (up ℤ)) =
        F.mapHomotopyCategoryFactors (up ℤ) := sorry

section TensorComparison

variable [HasBinaryBiproducts C]
variable [MonoidalCategory (CochainComplex C ℤ)]
variable [MonoidalCategory (CochainComplex D ℤ)]
variable [MonoidalCategory (HomotopyCategory C (up ℤ))]
variable [MonoidalCategory (HomotopyCategory D (up ℤ))]
variable [(HomotopyCategory.quotient C (up ℤ)).Monoidal]
variable [(HomotopyCategory.quotient D (up ℤ)).Monoidal]

/-- The tensor-of-images bifunctor on complexes, followed by the target homotopy quotient. -/
abbrev tensorPreQuotient :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤
      HomotopyCategory D (up ℤ) :=
  (Functor.postcompose₂.obj (HomotopyCategory.quotient D (up ℤ))).obj
    (curriedTensorPre (F.mapHomologicalComplex (up ℤ)))

/-- The image-of-tensor bifunctor on complexes, followed by the target homotopy quotient. -/
abbrev tensorPostQuotient :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ ⥤
      HomotopyCategory D (up ℤ) :=
  (Functor.postcompose₂.obj (HomotopyCategory.quotient D (up ℤ))).obj
    (curriedTensorPost (F.mapHomologicalComplex (up ℤ)))

/-- The factorization isomorphism exhibiting the homotopy-level tensor-of-images bifunctor as
the descent of its complex-level counterpart. -/
@[stacks 07A4 "tensor-of-images homotopy factorization"]
noncomputable def tensorPreFactors :
    (((Functor.whiskeringLeft₂ (HomotopyCategory D (up ℤ))).obj
        (HomotopyCategory.quotient C (up ℤ))).obj
      (HomotopyCategory.quotient C (up ℤ))).obj
        (curriedTensorPre (F.mapHomotopyCategory (up ℤ))) ≅
      tensorPreQuotient F :=
  curriedTensorPreFunctor.mapIso (F.mapHomotopyCategoryFactors (up ℤ)) ≪≫
    ((((Functor.whiskeringLeft₂ (HomotopyCategory D (up ℤ))).obj
        (F.mapHomologicalComplex (up ℤ))).obj
      (F.mapHomologicalComplex (up ℤ))).mapIso
        (Functor.curriedTensorPreIsoPost (HomotopyCategory.quotient D (up ℤ))))

/-- The factorization isomorphism exhibiting the homotopy-level image-of-tensor bifunctor as
the descent of its complex-level counterpart. -/
@[stacks 07A4 "image-of-tensor homotopy factorization"]
noncomputable def tensorPostFactors :
    (((Functor.whiskeringLeft₂ (HomotopyCategory D (up ℤ))).obj
        (HomotopyCategory.quotient C (up ℤ))).obj
      (HomotopyCategory.quotient C (up ℤ))).obj
        (curriedTensorPost (F.mapHomotopyCategory (up ℤ))) ≅
      tensorPostQuotient F :=
  (Functor.postcompose₂.obj (F.mapHomotopyCategory (up ℤ))).mapIso
      (Functor.curriedTensorPreIsoPost (HomotopyCategory.quotient C (up ℤ))) ≪≫
    curriedTensorPostFunctor.mapIso (F.mapHomotopyCategoryFactors (up ℤ))

/-- A unit isomorphism for the termwise functor descends explicitly through the two monoidal
homotopy quotient functors. -/
@[stacks 07A4 "homotopy-category unit isomorphism"]
noncomputable def unitIsoOfComp
    (e₀ : 𝟙_ (CochainComplex D ℤ) ≅
      (F.mapHomologicalComplex (up ℤ)).obj (𝟙_ (CochainComplex C ℤ))) :
    𝟙_ (HomotopyCategory D (up ℤ)) ≅
      (F.mapHomotopyCategory (up ℤ)).obj
        (𝟙_ (HomotopyCategory C (up ℤ))) :=
  Functor.Monoidal.εIso (HomotopyCategory.quotient D (up ℤ)) ≪≫
    (HomotopyCategory.quotient D (up ℤ)).mapIso e₀ ≪≫
    (F.mapHomotopyCategoryFactors (up ℤ)).symm.app
      (𝟙_ (CochainComplex C ℤ)) ≪≫
    (F.mapHomotopyCategory (up ℤ)).mapIso
      (Functor.Monoidal.εIso (HomotopyCategory.quotient C (up ℤ))).symm

/-- The canonical bifunctor lifting datum for tensoring the two mapped homotopy objects. -/
@[implicit_reducible]
noncomputable instance tensorPreLifting :
    Localization.Lifting₂
      (HomotopyCategory.quotient C (up ℤ))
      (HomotopyCategory.quotient C (up ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ) :
        MorphismProperty (CochainComplex C ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ) :
        MorphismProperty (CochainComplex C ℤ))
      (tensorPreQuotient F)
      (curriedTensorPre (F.mapHomotopyCategory (up ℤ))) where
  iso := tensorPreFactors F

/-- The canonical bifunctor lifting datum for mapping the tensor product of two homotopy
objects. -/
@[implicit_reducible]
noncomputable instance tensorPostLifting :
    Localization.Lifting₂
      (HomotopyCategory.quotient C (up ℤ))
      (HomotopyCategory.quotient C (up ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ) :
        MorphismProperty (CochainComplex C ℤ))
      (HomologicalComplex.homotopyEquivalences C (up ℤ) :
        MorphismProperty (CochainComplex C ℤ))
      (tensorPostQuotient F)
      (curriedTensorPost (F.mapHomotopyCategory (up ℤ))) where
  iso := tensorPostFactors F

/-- Postcomposition with the target homotopy quotient sends a complex-level tensor comparison
to a comparison between the two quotient-valued bifunctors. -/
noncomputable def quotientTensorComparisonNatTrans
    (τ : curriedTensorPre (F.mapHomologicalComplex (up ℤ)) ⟶
      curriedTensorPost (F.mapHomologicalComplex (up ℤ))) :
    tensorPreQuotient F ⟶ tensorPostQuotient F :=
  (Functor.postcompose₂.obj (HomotopyCategory.quotient D (up ℤ))).map τ

/-- A tensor comparison for the termwise functor descends canonically to a natural
transformation of bifunctors on homotopy categories.  No invertibility hypothesis is needed. -/
@[stacks 07A4 "homotopy-category tensor comparison transformation"]
noncomputable def tensorComparisonNatTrans
    (τ : curriedTensorPre (F.mapHomologicalComplex (up ℤ)) ⟶
      curriedTensorPost (F.mapHomologicalComplex (up ℤ))) :
    curriedTensorPre (F.mapHomotopyCategory (up ℤ)) ⟶
      curriedTensorPost (F.mapHomotopyCategory (up ℤ)) :=
  Localization.lift₂NatTrans
    (HomotopyCategory.quotient C (up ℤ))
    (HomotopyCategory.quotient C (up ℤ))
    (HomologicalComplex.homotopyEquivalences C (up ℤ) :
      MorphismProperty (CochainComplex C ℤ))
    (HomologicalComplex.homotopyEquivalences C (up ℤ) :
      MorphismProperty (CochainComplex C ℤ))
    (tensorPreQuotient F) (tensorPostQuotient F)
    (curriedTensorPre (F.mapHomotopyCategory (up ℤ)))
    (curriedTensorPost (F.mapHomotopyCategory (up ℤ)))
    (quotientTensorComparisonNatTrans F τ)

/-- On quotient objects, the descended tensor comparison is obtained by conjugating the
quotient of the complex-level component with the two canonical factorization isomorphisms. -/
@[simp]
theorem tensorComparisonNatTrans_app_app_quotient
    (τ : curriedTensorPre (F.mapHomologicalComplex (up ℤ)) ⟶
      curriedTensorPost (F.mapHomologicalComplex (up ℤ)))
    (K L : CochainComplex C ℤ) :
    ((tensorComparisonNatTrans F τ).app
      ((HomotopyCategory.quotient C (up ℤ)).obj K)).app
        ((HomotopyCategory.quotient C (up ℤ)).obj L) =
      ((tensorPreFactors F).hom.app K).app L ≫
        (HomotopyCategory.quotient D (up ℤ)).map ((τ.app K).app L) ≫
          ((tensorPostFactors F).inv.app K).app L := sorry

end TensorComparison

section Monoidal

variable [HasBinaryBiproducts C]
variable [MonoidalCategory (CochainComplex C ℤ)]
variable [MonoidalCategory (CochainComplex D ℤ)]
variable [MonoidalCategory (HomotopyCategory C (up ℤ))]
variable [MonoidalCategory (HomotopyCategory D (up ℤ))]
variable [(F.mapHomologicalComplex (up ℤ)).Monoidal]
variable [(HomotopyCategory.quotient C (up ℤ)).Monoidal]
variable [(HomotopyCategory.quotient D (up ℤ)).Monoidal]

/-- The strong monoidal core on the homotopy-category action of `F`, obtained from the universal
property of the source homotopy quotient. -/
@[stacks 07A4 "homotopy-category monoidal functor core"]
noncomputable def mapCoreMonoidal :
    (F.mapHomotopyCategory (up ℤ)).CoreMonoidal :=
  Localization.Monoidal.functorCoreMonoidalOfComp
    (HomotopyCategory.quotient C (up ℤ))
    (HomologicalComplex.homotopyEquivalences C (up ℤ) :
      MorphismProperty (CochainComplex C ℤ))
    (F.mapHomotopyCategory (up ℤ))
    (F.mapHomologicalComplex (up ℤ) ⋙ HomotopyCategory.quotient D (up ℤ))

/-- A strong monoidal structure on the homotopy-category action, obtained from supplied strong
monoidal structures on the termwise functor and the quotient functors. This is explicit data rather
than an instance so that a more intrinsic descended tensor comparison may be installed downstream. -/
@[stacks 07A4 "homotopy-category monoidal functor", implicit_reducible]
noncomputable def mapMonoidal :
    (F.mapHomotopyCategory (up ℤ)).Monoidal :=
  (mapCoreMonoidal F).toMonoidal

/-- The canonical unit isomorphism for the induced functor on homotopy categories. -/
noncomputable abbrev mapUnitIso :
    𝟙_ (HomotopyCategory D (up ℤ)) ≅
      (F.mapHomotopyCategory (up ℤ)).obj
        (𝟙_ (HomotopyCategory C (up ℤ))) :=
  (mapCoreMonoidal F).εIso

/-- The canonical tensorator for the induced functor on homotopy categories. -/
@[stacks 07A4 "homotopy-category tensorator"]
noncomputable abbrev mapTensorIso
    (K L : HomotopyCategory C (up ℤ)) :
    (F.mapHomotopyCategory (up ℤ)).obj K ⊗
        (F.mapHomotopyCategory (up ℤ)).obj L ≅
      (F.mapHomotopyCategory (up ℤ)).obj (K ⊗ L) :=
  (mapCoreMonoidal F).μIso K L

/-- The tensor-preservation isomorphism in the source-facing direction. -/
@[stacks 07A4 "homotopy-category tensor preservation"]
noncomputable abbrev preservesTensorIso
    (K L : HomotopyCategory C (up ℤ)) :
    (F.mapHomotopyCategory (up ℤ)).obj (K ⊗ L) ≅
      (F.mapHomotopyCategory (up ℤ)).obj K ⊗
        (F.mapHomotopyCategory (up ℤ)).obj L :=
  (mapTensorIso F K L).symm

end Monoidal

end CategoryTheory.Functor.Homotopy
