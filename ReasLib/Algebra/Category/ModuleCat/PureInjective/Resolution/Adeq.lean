module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.Abelian.Subcategory
public import ReasLib.Algebra.Homology.CochainComplex.HomComplex.Comparison
public import ReasLib.Algebra.Homology.Embedding.Functor
public import ReasLib.CategoryTheory.Preadditive.HomCongr
public import ReasLib.Algebra.Category.ModuleCat.PureExt
public import ReasLib.Algebra.Category.ModuleCat.PureInjective.Resolution.PureExt
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.TensorExtension

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe w u

namespace ModuleCat.PureInjectiveCoresolution

variable {A : CommRingCat.{u}} {N : ModuleCat.{u} A}

/-- The augmentation of a pure injective resolution, bundled as a morphism from the
degree-zero cochain complex. -/
noncomputable def augmentation (I : PureInjectiveCoresolution N) :
    (CochainComplex.single₀ (ModuleCat.{u} A)).obj N ⟶ I.cocomplex :=
  (CochainComplex.fromSingle₀Equiv I.cocomplex N).symm ⟨I.ι, I.ι_d⟩

/-- The degree-zero component of the bundled augmentation is the original augmentation. -/
theorem augmentation_f_zero (I : PureInjectiveCoresolution N) :
    I.augmentation.f 0 = I.ι := sorry

/-- The tensor-extension image of the nonnegative complex in a pure injective resolution. -/
noncomputable def adeqCocomplex [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) :
    CochainComplex (ModuleValuedFunctor.TensorAdeq A) ℕ :=
  ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj I.cocomplex

/-- Each term of the tensor-extended cocomplex is the tensor extension of the
corresponding module in the chosen resolution. -/
theorem adeqCocomplex_X [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) (n : ℕ) :
    I.adeqCocomplex.X n =
      (ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj (I.cocomplex.X n) := sorry

/-- Tensor extension sends every term of a pure injective resolution to an injective
adequate module-valued functor. -/
theorem adeqResolutionTermInjective [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) (n : ℕ) :
    Injective (I.adeqCocomplex.X n) := sorry

/-- The mapped augmentation of a pure injective resolution is a quasi-isomorphism in the
category of adequate module-valued functors. -/
theorem adeqResolutionAugmentationQuasiIso
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) :
    QuasiIso
      ((HomologicalComplex.singleMapHomologicalComplex
          (ModuleValuedFunctor.TensorAdeq.tensorExtension A) (ComplexShape.up ℕ) 0).inv.app N ≫
        ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomologicalComplex
          (ComplexShape.up ℕ)).map I.augmentation) := sorry

/-- The injective resolution in adequate module-valued functors obtained by tensor-extending
a chosen pure injective resolution. -/
noncomputable def adeqResolution [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) :
    InjectiveResolution ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj N) where
  cocomplex :=
    I.adeqCocomplex
  injective n := adeqResolutionTermInjective I n
  ι :=
    (HomologicalComplex.singleMapHomologicalComplex
      (ModuleValuedFunctor.TensorAdeq.tensorExtension A) (ComplexShape.up ℕ) 0).inv.app N ≫
        ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomologicalComplex
          (ComplexShape.up ℕ)).map I.augmentation
  quasiIso := adeqResolutionAugmentationQuasiIso I

/-- The cocomplex of `adeqResolution` is the termwise tensor extension of the chosen pure
injective resolution. -/
theorem adeqResolution_cocomplex [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) :
    I.adeqResolution.cocomplex = I.adeqCocomplex := sorry

/-- Tensor extension commutes canonically with extension of a pure injective resolution from
natural to integer cochain degrees. -/
noncomputable def mapCochainComplexIso [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) :
    (((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.cochainComplex) ≅ I.adeqResolution.cochainComplex :=
  ComplexShape.embeddingUpNat.mapAppIso
    (ModuleValuedFunctor.TensorAdeq.tensorExtension A) I.cocomplex

/-- Tensor extension commutes with both integer-degree extension and a subsequent shift of
the chosen pure injective resolution. -/
noncomputable def mapShiftedCochainComplexIso
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) (i : ℤ) :
    ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (I.cochainComplex⟦i⟧) ≅
        (I.adeqResolution.cochainComplex⟦i⟧) :=
  (((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomologicalComplex
      (ComplexShape.up ℤ)).commShiftIso i).app I.cochainComplex ≪≫
    (CategoryTheory.shiftFunctor (CochainComplex (ModuleValuedFunctor.TensorAdeq A) ℤ) i).mapIso
      I.mapCochainComplexIso

/-- The source comparison used when tensor extension is applied to a shifted-Hom
representative of pure Ext. -/
noncomputable def mapSingleHomotopyIso [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (M : ModuleCat.{u} A) :
    ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)) ≅
      (HomotopyCategory.quotient (ModuleValuedFunctor.TensorAdeq A)
        (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor (ModuleValuedFunctor.TensorAdeq A) 0).obj
            ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M)) :=
  (HomotopyCategory.quotient (ModuleValuedFunctor.TensorAdeq A)
    (ComplexShape.up ℤ)).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleValuedFunctor.TensorAdeq.tensorExtension A) (ComplexShape.up ℤ) 0).app M)

/-- The target comparison used when tensor extension is applied to a shifted-Hom
representative from a chosen pure injective resolution. -/
noncomputable def mapShiftedHomotopyIso
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) (i : ℤ) :
    ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomotopyCategory
      (ComplexShape.up ℤ)).obj
        ((HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
          (I.cochainComplex⟦i⟧)) ≅
      (HomotopyCategory.quotient (ModuleValuedFunctor.TensorAdeq A)
        (ComplexShape.up ℤ)).obj (I.adeqResolution.cochainComplex⟦i⟧) :=
  (HomotopyCategory.quotient (ModuleValuedFunctor.TensorAdeq A)
    (ComplexShape.up ℤ)).mapIso (I.mapShiftedCochainComplexIso i)

/-- The additive map from pure Ext computed by a chosen pure injective resolution to Ext in
the adequate-functor category. It maps shifted-Hom representatives by tensor extension. -/
noncomputable def resolutionComparisonAddHom
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    (I : PureInjectiveCoresolution N) (M : ModuleCat.{u} A) (i : ℕ) :
    I.pureExt M i →+
      Abelian.Ext ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M)
        ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj N) i :=
  let sourceEquiv :=
    CochainComplex.HomComplex.Module.homologyHomAddEquiv A
      ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M)
      I.cochainComplex (i : ℤ)
  let mappedHom :=
    Functor.mapAddHom
      (F := (ModuleValuedFunctor.TensorAdeq.tensorExtension A).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (X := (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj M))
      (Y := (HomotopyCategory.quotient (ModuleCat.{u} A) (ComplexShape.up ℤ)).obj
        (I.cochainComplex⟦(i : ℤ)⟧))
  let transportedHom :=
    Iso.homCongrAddEquiv (mapSingleHomotopyIso M) (I.mapShiftedHomotopyIso i)
  let targetHomEquiv :=
    (CochainComplex.HomComplex.homologyHomAddEquiv
      ((CochainComplex.singleFunctor (ModuleValuedFunctor.TensorAdeq A) 0).obj
        ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M))
      I.adeqResolution.cochainComplex (i : ℤ)).symm
  let targetClassEquiv :=
    CochainComplex.HomComplex.homologyAddEquiv
      ((CochainComplex.singleFunctor (ModuleValuedFunctor.TensorAdeq A) 0).obj
        ((ModuleValuedFunctor.TensorAdeq.tensorExtension A).obj M))
      I.adeqResolution.cochainComplex (i : ℤ)
  I.adeqResolution.extAddEquivCohomologyClass.symm.toAddMonoidHom.comp
    (targetClassEquiv.toAddMonoidHom.comp
      (targetHomEquiv.toAddMonoidHom.comp
        (transportedHom.toAddMonoidHom.comp
          (mappedHom.comp sourceEquiv.toAddMonoidHom))))

/-- The comparison from a chosen-resolution computation of pure Ext to the canonical value of
the functorial pure Ext bifunctor. -/
noncomputable def resolutionComparison
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    [UnivLE.{u, w}]
    (I : PureInjectiveCoresolution N) (M : ModuleCat.{u} A) (i : ℕ) :
    AddCommGrpCat.of (Shrink.{w} (I.pureExt M i : Type u)) ⟶
      ((ModuleCat.PureExt.functor.{w, u} A i).obj (op M)).obj N :=
  AddCommGrpCat.ofHom
    ((I.resolutionComparisonAddHom M i).comp Shrink.addEquiv.toAddMonoidHom)

/-- The chosen-resolution comparison to functorial pure Ext is an isomorphism. -/
theorem resolutionComparisonIsIso
    [Abelian (ModuleValuedFunctor.TensorAdeq A)]
    [HasExt.{w} (ModuleValuedFunctor.TensorAdeq A)]
    [hAdd : (ModuleValuedFunctor.TensorAdeq.tensorExtension A).Additive]
    [UnivLE.{u, w}]
    (I : PureInjectiveCoresolution N) (M : ModuleCat.{u} A) (i : ℕ) :
    IsIso (I.resolutionComparison M i) := sorry

end ModuleCat.PureInjectiveCoresolution
