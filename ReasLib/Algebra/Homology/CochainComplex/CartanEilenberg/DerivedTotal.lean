module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.TotalFunctoriality
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Homology.Below
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cohomology
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.KInjective.Bounded
public import ReasLib.CategoryTheory.Functor.Derived.ComputesAt.Total
public import ReasLib.CategoryTheory.Homology.DoubleComplex.Filtration

/-!
# Computing Bounded-Below Right Derived Functors by Cartan--Eilenberg Totals

The total complex of a Cartan--Eilenberg resolution is a bounded-below complex of injectives.
This file connects that concrete model to the canonical pointwise and total right-derived APIs
for an arbitrary functor out of the bounded-below homotopy category.
-/

@[expose] public section

open CategoryTheory Limits ComplexShape

noncomputable section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u₁} [Category.{v₁} A] [Abelian A]
variable {K : CochainComplex.Plus A} (I : CartanEilenbergResolution K)

/-- The Cartan--Eilenberg augmentation to the total complex, regarded as a morphism of
bounded-below cochain complexes. -/
noncomputable def Total.augmentationPlus :
    K ⟶ (Total.toInjectivePlus I : CochainComplex.Plus A) :=
  ⟨Total.augmentation I⟩

/-- Forgetting bounded-below packaging from `Total.augmentationPlus` recovers the canonical
augmentation to the total complex. -/
@[simp]
theorem Total.augmentationPlus_forget :
    (CochainComplex.Plus.ι A).map (Total.augmentationPlus I) =
      Total.augmentation I := sorry

/-- The Cartan--Eilenberg augmentation to the total complex in the bounded-below homotopy
category. -/
noncomputable def Total.augmentationHomotopy :
    (HomotopyCategory.Plus.quotient A).obj K ⟶
      (HomotopyCategory.Plus.quotient A).obj
        (Total.toInjectivePlus I : CochainComplex.Plus A) :=
  (HomotopyCategory.Plus.quotient A).map (Total.augmentationPlus I)

/-- The Cartan--Eilenberg augmentation to the total complex is a quasi-isomorphism in the
bounded-below homotopy category. -/
theorem Total.augmentationHomotopy_quasiIso :
    HomotopyCategory.Plus.quasiIso A (Total.augmentationHomotopy I) := sorry

/-- Every localization at bounded-below quasi-isomorphisms sends the Cartan--Eilenberg
augmentation to an isomorphism between the original complex and its total injective model. -/
noncomputable def Total.augmentationLocalizationIso
    {E : Type u₂} [Category.{v₂} E] (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)] :
    Q.obj ((HomotopyCategory.Plus.quotient A).obj K) ≅
      Q.obj ((HomotopyCategory.Plus.quotient A).obj
        (Total.toInjectivePlus I : CochainComplex.Plus A)) :=
  Localization.isoOfHom
    Q
    (HomotopyCategory.Plus.quasiIso A)
    (Total.augmentationHomotopy I)
    (Total.augmentationHomotopy_quasiIso I)

section Computation

variable {D : Type u₂} [Category.{v₂} D]
variable (G : HomotopyCategory.Plus A ⥤ D)

/-- The total injective complex of a Cartan--Eilenberg resolution computes the pointwise
right-derived value of every functor out of `K⁺(A)`. -/
@[stacks 015H "the total Cartan-Eilenberg complex computes right derived functors"]
theorem Total.computesRightDerivedAt :
    CategoryTheory.Functor.RightDerived.ComputesAt G (HomotopyCategory.Plus.quasiIso A)
      ((HomotopyCategory.Plus.quotient A).obj
        (Total.toInjectivePlus I : CochainComplex.Plus A)) := sorry

variable [G.HasRightDerivedFunctor (HomotopyCategory.Plus.quasiIso A)]

/-- Evaluation on the Cartan--Eilenberg total injective model is canonically isomorphic to the
total right-derived value at the original bounded-below complex. -/
@[stacks 015H "Cartan-Eilenberg total computation of the right derived functor"]
noncomputable def Total.rightDerivedIso
    {E : Type u₃} [Category.{v₃} E] (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)] :
    G.obj
        ((HomotopyCategory.Plus.quotient A).obj
          (Total.toInjectivePlus I : CochainComplex.Plus A)) ≅
      Functor.RightDerived.Bounded.value G Q K :=
  CategoryTheory.Functor.RightDerived.ComputesAt.replacementIso G
    (HomotopyCategory.Plus.quasiIso A) Q
    (Total.augmentationHomotopy I) (Total.augmentationHomotopy_quasiIso I)
    (Total.computesRightDerivedAt I G)

/-- The forward map of `Total.rightDerivedIso` is the right-derived unit on the total injective
model followed by transport along the localized Cartan--Eilenberg augmentation. -/
theorem Total.rightDerivedIso_hom
    {E : Type u₃} [Category.{v₃} E] (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)] :
    (Total.rightDerivedIso I G Q).hom =
      (G.totalRightDerivedUnit
          Q
          (HomotopyCategory.Plus.quasiIso A)).app
            ((HomotopyCategory.Plus.quotient A).obj
              (Total.toInjectivePlus I : CochainComplex.Plus A)) ≫
            (G.totalRightDerived
          Q
          (HomotopyCategory.Plus.quasiIso A)).map
            (Total.augmentationLocalizationIso I Q).inv := sorry

/-- The inverse Cartan--Eilenberg total comparison first transports along the localized
augmentation and then uses the inverse derived unit on the total injective model. -/
theorem Total.rightDerivedIso_inv
    {E : Type u₃} [Category.{v₃} E] (Q : HomotopyCategory.Plus A ⥤ E)
    [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)] :
    (Total.rightDerivedIso I G Q).inv =
      (G.totalRightDerived Q (HomotopyCategory.Plus.quasiIso A)).map
          (Total.augmentationLocalizationIso I Q).hom ≫
        (CategoryTheory.Functor.RightDerived.ComputesAt.unitIso G
          (HomotopyCategory.Plus.quasiIso A) Q
          ((HomotopyCategory.Plus.quotient A).obj
            (Total.toInjectivePlus I : CochainComplex.Plus A))
          (Total.computesRightDerivedAt I G)).inv := sorry

end Computation

section MappedHomology

variable {B : Type u₂} [Category.{v₂} B] [Abelian B]
variable (F : A ⥤ B) [F.Additive] [HasDerivedCategory.{w} B]
variable {E : Type u₃} [Category.{v₃} E]
variable (Q : HomotopyCategory.Plus A ⥤ E)
variable [Q.IsLocalization (HomotopyCategory.Plus.quasiIso A)]
variable [Functor.RightDerived.EverywhereDefined F.toBoundedBelowDerived
  (HomotopyCategory.Plus.quasiIso A)]

namespace MappedTotal

/-- Applying an additive functor termwise to a Cartan--Eilenberg resolution and then taking
the cohomology of its total complex computes the cohomology of the total right-derived value.
The localization functor is arbitrary, so this comparison applies directly to any chosen
bounded-below derived-category model. -/
@[stacks 015H "cohomology of a mapped Cartan-Eilenberg total"]
noncomputable def homologyIso (n : ℤ) :
    ((I.mapBicomplex F).total (up ℤ)).homology n ≅
      Functor.RightDerived.Bounded.cohomology F Q K n :=
  (HomologicalComplex.homologyFunctor B (up ℤ) n).mapIso (MappedTotal.iso I F) ≪≫
    Functor.Homotopy.Plus.Homology.homologyIso F
      (Total.toInjectivePlus I : CochainComplex.Plus A) n ≪≫
    (DerivedCategory.Plus.homologyFunctor B n).mapIso
      (Total.rightDerivedIso I F.toBoundedBelowDerived Q)

/-- The forward mapped-total comparison is the totalization comparison, followed by the generic
bounded-below homology bridge and the total right-derived comparison. -/
@[simp]
theorem homologyIso_hom (n : ℤ) :
    (homologyIso I F Q n).hom =
      (HomologicalComplex.homologyFunctor B (up ℤ) n).map
          (MappedTotal.iso I F).hom ≫
        (Functor.Homotopy.Plus.Homology.homologyIso F
          (Total.toInjectivePlus I : CochainComplex.Plus A) n).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n).map
          (Total.rightDerivedIso I F.toBoundedBelowDerived Q).hom := sorry

/-- The inverse mapped-total comparison reverses the right-derived, bounded-below homology, and
totalization comparisons. -/
@[simp]
theorem homologyIso_inv (n : ℤ) :
    (homologyIso I F Q n).inv =
      (DerivedCategory.Plus.homologyFunctor B n).map
          (Total.rightDerivedIso I F.toBoundedBelowDerived Q).inv ≫
        (Functor.Homotopy.Plus.Homology.homologyIso F
          (Total.toInjectivePlus I : CochainComplex.Plus A) n).inv ≫
        (HomologicalComplex.homologyFunctor B (up ℤ) n).map
          (MappedTotal.iso I F).inv := sorry

end MappedTotal

end MappedHomology

end CochainComplex.CartanEilenbergResolution
