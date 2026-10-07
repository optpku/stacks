module

public import ReasLib.Algebra.Homology.DerivedCategory.Completeness.LocalizationAway
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Functoriality
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction.Single
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.Flat
public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.ProjectionFormula
public import ReasLib.Algebra.Module.LocalizedModule.Away.BaseChange
public import ReasLib.Algebra.Module.LocalizedModule.Away.Iterated.Equiv
import Mathlib.Tactic.CrossRefAttribute

/-!
# Iterating localization-away derived internal Hom

@stack 0A6C

The projection formula identifies the derived tensor of the degree-zero principal localizations
at `f` and `g` with the degree-zero localization at `f * g`.  Currying then identifies iterated
localization-away internal Hom with localization away from the product.

The selected closed structure and fixed-right tensor model remain explicit: neither is canonical
from the ambient derived category alone.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open scoped CategoryTheory.DerivedCategory.DerivedTensor _root_.DerivedInternalHom

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.LocalizationAway

variable {A : Type u} [CommRing A]

/-- Successive localization first at `g` and then at `f`, normalized to localization at
`f * g`. -/
@[stacks 0A6C "successive principal localization at a product"]
noncomputable def iteratedLinearEquiv (f g : A) :
    LocalizedModule.Away f (LocalizedModule.Away g A) ≃ₗ[A]
      LocalizedModule.Away (f * g) A :=
  (LocalizedModule.Away.Iterated.baseMulEquiv g f A).trans
    (LocalizedModule.Away.Iterated.denominatorEquiv A (mul_comm g f))

/-- The underlying additive isomorphism for the restricted successive-localization comparison. -/
@[stacks 0A6C "restricted successive localization additive comparison"]
noncomputable def restrictedIteratedAddIso (f g : A) :
    (forget₂ (ModuleCat A) Ab).obj
        ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of (Localization.Away f)
            (LocalizedModule.Away f (LocalizedModule.Away g A)))) ≅
      (forget₂ (ModuleCat A) Ab).obj
        (ModuleCat.of A (LocalizedModule.Away (f * g) A)) :=
  (iteratedLinearEquiv f g).toAddEquiv.toAddCommGrpIso

/-- The restricted successive-localization additive comparison respects the `A`-action. -/
@[stacks 0A6C "restricted successive localization scalar compatibility"]
theorem restrictedIteratedAddIso_smul (f g r : A) :
    (restrictedIteratedAddIso f g).hom ≫
        (ModuleCat.of A (LocalizedModule.Away (f * g) A)).smul r =
      ((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
        (ModuleCat.of (Localization.Away f)
          (LocalizedModule.Away f (LocalizedModule.Away g A)))).smul r ≫
        (restrictedIteratedAddIso f g).hom := by
  ext x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  have hφ (y : LocalizedModule.Away f (LocalizedModule.Away g A)) :
      (ConcreteCategory.hom (restrictedIteratedAddIso f g).hom) y =
        iteratedLinearEquiv f g y := rfl
  have ht (y : LocalizedModule.Away (f * g) A) :
      (ConcreteCategory.hom
        ((ModuleCat.of A (LocalizedModule.Away (f * g) A)).smul r)) y = r • y := rfl
  have hs (y : LocalizedModule.Away f (LocalizedModule.Away g A)) :
      (ConcreteCategory.hom
        (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of (Localization.Away f)
            (LocalizedModule.Away f (LocalizedModule.Away g A)))).smul r)) y =
        (algebraMap A (Localization.Away f) r) • y := rfl
  rw [hφ, ht, hs, IsScalarTower.algebraMap_smul, hφ]
  exact ((iteratedLinearEquiv f g).map_smul r
    (show LocalizedModule.Away f (LocalizedModule.Away g A) from x)).symm

/-- Restricting the successive principal localization to `A` gives the product localization. -/
@[stacks 0A6C "restricted successive principal localization comparison"]
noncomputable def restrictedIteratedIso (f g : A) :
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
        (ModuleCat.of (Localization.Away f)
          (LocalizedModule.Away f (LocalizedModule.Away g A))) ≅
      ModuleCat.of A (LocalizedModule.Away (f * g) A) :=
  ModuleCat.isoMk (restrictedIteratedAddIso f g)
    (restrictedIteratedAddIso_smul f g)

/-- Extension to `A_f` followed by restriction identifies `A_g` with the successive
localization, hence with `A_{fg}`. -/
@[stacks 0A6C "extension-restriction comparison for principal localizations"]
noncomputable def extensionRestrictionIso (f g : A) :
    (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).obj
        ((ModuleCat.extendScalars (algebraMap A (Localization.Away f))).obj
          (ModuleCat.of A (Localization.Away g))) ≅
      ModuleCat.of A (Localization.Away (f * g)) :=
  (ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapIso
      (ModuleCat.ExtendScalars.awayIso f (ModuleCat.of A (Localization.Away g))) ≪≫
    restrictedIteratedIso f g

/-- Flat derived extension to a principal localization commutes with the degree-zero single
functor. -/
@[stacks 0A6C "principal localization derived extension of a single object"]
noncomputable def extensionSingleIso (f : A) (M : ModuleCat A) :
    (CategoryTheory.ModuleCat.derivedExtensionOfScalars
      (algebraMap A (Localization.Away f))).obj (ModuleCat.single0 M) ≅
      ModuleCat.single0
        ((ModuleCat.extendScalars (algebraMap A (Localization.Away f))).obj M) :=
  let hf : (algebraMap A (Localization.Away f)).Flat :=
    RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat (Localization.Away f) (Submonoid.powers f))
  ((CategoryTheory.ModuleCat.DerivedExtension.Flat.mapDerivedCategoryComparisonIso
      (algebraMap A (Localization.Away f)) hf).app (ModuleCat.single0 M)).symm ≪≫
    ((CategoryTheory.Functor.mapDerivedCategorySingleFunctor
      (ModuleCat.ExtendScalars.exact (algebraMap A (Localization.Away f)) hf).obj
      (0 : ℤ)).app M)

/-- The additive comparison between the restricted regular `A_f`-module and `A_f` as an
`A`-module. -/
@[stacks 0A6C "restricted regular localization additive comparison"]
noncomputable def restrictedRegularAddIso (f : A) :
    (forget₂ (ModuleCat A) Ab).obj
        (CategoryTheory.ModuleCat.restrictedRegular
          (algebraMap A (Localization.Away f))) ≅
      (forget₂ (ModuleCat A) Ab).obj
        (ModuleCat.of A (Localization.Away f)) :=
  (CategoryTheory.ModuleCat.RestrictScalars.regularEquiv
    (A := A) (B := Localization.Away f)).toAddEquiv.toAddCommGrpIso

/-- The restricted regular localization comparison respects the `A`-action. -/
@[stacks 0A6C "restricted regular localization scalar compatibility"]
theorem restrictedRegularAddIso_smul (f r : A) :
    (restrictedRegularAddIso f).hom ≫
        (ModuleCat.of A (Localization.Away f)).smul r =
      (CategoryTheory.ModuleCat.restrictedRegular
        (algebraMap A (Localization.Away f))).smul r ≫
        (restrictedRegularAddIso f).hom := by
  ext x
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  have hφ (y : CategoryTheory.ModuleCat.restrictedRegular
      (algebraMap A (Localization.Away f))) :
      (ConcreteCategory.hom (restrictedRegularAddIso f).hom) y =
        CategoryTheory.ModuleCat.RestrictScalars.regularEquiv
          (A := A) (B := Localization.Away f) y := rfl
  have ht (y : Localization.Away f) :
      (ConcreteCategory.hom
        ((ModuleCat.of A (Localization.Away f)).smul r)) y = r • y := rfl
  have hs (y : CategoryTheory.ModuleCat.restrictedRegular
      (algebraMap A (Localization.Away f))) :
      (ConcreteCategory.hom
        ((CategoryTheory.ModuleCat.restrictedRegular
          (algebraMap A (Localization.Away f))).smul r)) y = r • y := rfl
  rw [hφ, ht, hs, hφ]
  exact (CategoryTheory.ModuleCat.RestrictScalars.regularEquiv
    (A := A) (B := Localization.Away f)).map_smul r
      (show CategoryTheory.ModuleCat.restrictedRegular
        (algebraMap A (Localization.Away f)) from x) |>.symm

/-- The restricted regular `A_f`-module is canonically the localization `A_f` as an
`A`-module. -/
@[stacks 0A6C "restricted regular principal-localization module comparison"]
noncomputable def restrictedRegularIso (f : A) :
    CategoryTheory.ModuleCat.restrictedRegular
        (algebraMap A (Localization.Away f)) ≅
      ModuleCat.of A (Localization.Away f) :=
  ModuleCat.isoMk (restrictedRegularAddIso f) (restrictedRegularAddIso_smul f)

/-- Degree-zero embedding of the restricted regular principal-localization comparison. -/
@[stacks 0A6C "restricted regular principal-localization single comparison"]
noncomputable def restrictedRegularSingleIso (f : A) :
    CategoryTheory.ModuleCat.restrictedRegular₀
        (algebraMap A (Localization.Away f)) ≅
      ModuleCat.single0 (ModuleCat.of A (Localization.Away f)) :=
  (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).mapIso
    (restrictedRegularIso f)

end CategoryTheory.ModuleCat.LocalizationAway

namespace CategoryTheory.DerivedCategory.LocalizationAway

variable {A : Type u} [CommRing A]

/-- The derived tensor of the degree-zero localizations at `f` and `g` is the degree-zero
localization at `f * g`. -/
@[stacks 0A6C "derived tensor of principal localizations"]
noncomputable def tensorIso (f g : A) :
    DerivedTensor.Right.obj
        (ModuleCat.single0 (ModuleCat.of A (Localization.Away f)))
        (ModuleCat.single0 (ModuleCat.of A (Localization.Away g))) ≅
      ModuleCat.single0 (ModuleCat.of A (Localization.Away (f * g))) :=
  let σ := algebraMap A (Localization.Away f)
  (CategoryTheory.DerivedCategory.derivedTensorProduct
      (ModuleCat.single0 (ModuleCat.of A (Localization.Away g)))).mapIso
        (ModuleCat.LocalizationAway.restrictedRegularSingleIso f).symm ≪≫
    (CategoryTheory.ModuleCat.restrictDerivedTensorIso σ
      (ModuleCat.single0 (ModuleCat.of A (Localization.Away g)))).symm ≪≫
    (CategoryTheory.ModuleCat.derivedRestrictionOfScalars σ).mapIso
      (ModuleCat.LocalizationAway.extensionSingleIso f
        (ModuleCat.of A (Localization.Away g))) ≪≫
    CategoryTheory.ModuleCat.DerivedRestriction.singleIso σ (0 : ℤ)
      ((ModuleCat.extendScalars σ).obj
        (ModuleCat.of A (Localization.Away g))) ≪≫
    (DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).mapIso
      (ModuleCat.LocalizationAway.extensionRestrictionIso f g)

end CategoryTheory.DerivedCategory.LocalizationAway

namespace CategoryTheory.DerivedCategory

section Closed

variable {A : Type u} [CommRing A]
variable [MonoidalCategory (DerivedCategory (ModuleCat A))]
variable [BraidedCategory (DerivedCategory (ModuleCat A))]
variable [DerivedTensor.Right.Has (C := ModuleCat A)]

/-- Lemma 15.92.9 (0A6C): iterating localization-away derived internal Hom at `g` and then
at `f` is localization-away derived internal Hom at `f * g`. -/
@[stacks 0A6C "iterated localization-away derived internal Hom"]
noncomputable def localizationAwayT_mulIso
    (H : MonoidalClosed (DerivedCategory (ModuleCat A)))
    (T : DerivedTensor.Right.Monoidal.Model (C := ModuleCat A))
    (f g : A) (K : DerivedCategory (ModuleCat A)) :
    localizationAwayT H f (localizationAwayT H g K) ≅
      localizationAwayT H (f * g) K :=
  InternalHom.TensorSource.isoOf H T
      (ModuleCat.single0 (ModuleCat.of A (Localization.Away f)))
      (ModuleCat.single0 (ModuleCat.of A (Localization.Away g))) K ≪≫
    MonoidalClosed.internalHomMapIsoOf H (LocalizationAway.tensorIso f g).symm
      (Iso.refl K)

end Closed

end CategoryTheory.DerivedCategory
