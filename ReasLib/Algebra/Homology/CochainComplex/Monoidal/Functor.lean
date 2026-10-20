/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import ReasLib.CategoryTheory.Homology.DoubleComplex.MapTotal.PreservesColimits
public import Mathlib.CategoryTheory.Monoidal.Multifunctor
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Monoidal functors on cochain complexes

An additive lax monoidal functor acts termwise on cochain complexes.  This file constructs its
unit and tensor comparison maps explicitly.  The tensor comparison first applies the base
tensorator in every bidegree and then uses the canonical comparison between an additive functor
and totalization.

Invertibility is deliberately kept separate from the comparison data: for unbounded complexes it
depends on the functor preserving the coproducts occurring in each total degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor.Cochain

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
variable (F : C ⥤ D) [F.Additive] [F.Monoidal]

/-- Apply an additive functor termwise to an unbounded cochain complex. -/
abbrev map : CochainComplex C ℤ ⥤ CochainComplex D ℤ :=
  F.mapHomologicalComplex (up ℤ)

/-- The pointwise tensor bicomplex of two cochain complexes. -/
abbrev tensorBicomplex (K L : CochainComplex C ℤ) :
    HomologicalComplex₂ C (up ℤ) (up ℤ) :=
  (((curriedTensor C).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj K).obj L

/-- The pointwise tensor bicomplex after applying `F` to both cochain complexes. -/
abbrev tensorBicomplexMap (K L : CochainComplex C ℤ) :
    HomologicalComplex₂ D (up ℤ) (up ℤ) :=
  (((curriedTensor D).mapBifunctorHomologicalComplex (up ℤ) (up ℤ)).obj
    ((map F).obj K)).obj ((map F).obj L)

/-- The termwise image under `F` of the pointwise tensor bicomplex. -/
abbrev mappedTensorBicomplex (K L : CochainComplex C ℤ) :
    HomologicalComplex₂ D (up ℤ) (up ℤ) :=
  (F.mapHomologicalComplex₂ (up ℤ) (up ℤ)).obj (tensorBicomplex K L)

/-- The base tensorator in bidegree `(p, q)`. -/
abbrev pointwiseTensorComponent (K L : CochainComplex C ℤ) (p q : ℤ) :
    (tensorBicomplexMap F K L).toGradedObject ⟨p, q⟩ ⟶
      (mappedTensorBicomplex F K L).toGradedObject ⟨p, q⟩ :=
  LaxMonoidal.μ F (K.X p) (L.X q)

/-- The pointwise tensorator commutes with the differential in the first direction. -/
theorem pointwiseTensorComponent_comm₁ (K L : CochainComplex C ℤ)
    (p p' q : ℤ) (h : (up ℤ).Rel p p') :
    pointwiseTensorComponent F K L p q ≫
        ((mappedTensorBicomplex F K L).d p p').f q =
      ((tensorBicomplexMap F K L).d p p').f q ≫
        pointwiseTensorComponent F K L p' q := sorry

/-- The pointwise tensorator commutes with the differential in the second direction. -/
theorem pointwiseTensorComponent_comm₂ (K L : CochainComplex C ℤ)
    (p q q' : ℤ) (h : (up ℤ).Rel q q') :
    pointwiseTensorComponent F K L p q ≫
        ((mappedTensorBicomplex F K L).X p).d q q' =
      ((tensorBicomplexMap F K L).X p).d q q' ≫
        pointwiseTensorComponent F K L p q' := sorry

/-- The base tensorator assembled into an isomorphism of columns of the pointwise tensor
bicomplexes. -/
noncomputable def tensorBicomplexColumnIso (K L : CochainComplex C ℤ) (p : ℤ) :
    (tensorBicomplexMap F K L).X p ≅ (mappedTensorBicomplex F K L).X p :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q ↦ Monoidal.μIso F (K.X p) (L.X q))
    (pointwiseTensorComponent_comm₂ F K L p)

/-- The columnwise tensorator is natural with respect to the differential in the first
bicomplex direction. -/
theorem tensorBicomplexColumnIso_natural (K L : CochainComplex C ℤ)
    (p p' : ℤ) (h : (up ℤ).Rel p p') :
    (tensorBicomplexColumnIso F K L p).hom ≫ (mappedTensorBicomplex F K L).d p p' =
      (tensorBicomplexMap F K L).d p p' ≫
        (tensorBicomplexColumnIso F K L p').hom := sorry

/-- The pointwise tensor bicomplex of the mapped complexes is canonically isomorphic to the
termwise image of the original pointwise tensor bicomplex. -/
@[stacks 07A4 "pointwise cochain-complex tensor isomorphism"]
noncomputable def tensorBicomplexIso (K L : CochainComplex C ℤ) :
    tensorBicomplexMap F K L ≅ mappedTensorBicomplex F K L :=
  HomologicalComplex.Hom.isoOfComponents
    (tensorBicomplexColumnIso F K L)
    (tensorBicomplexColumnIso_natural F K L)

/-- The canonical unit isomorphism for the termwise action of a monoidal additive functor. -/
@[stacks 07A4 "cochain-complex unit isomorphism"]
noncomputable def unitIso :
    HomologicalComplex.tensorUnit D (up ℤ) ≅
      (map F).obj (HomologicalComplex.tensorUnit C (up ℤ)) :=
  (HomologicalComplex.single D (up ℤ) 0).mapIso (Monoidal.εIso F) ≪≫
    ((HomologicalComplex.singleMapHomologicalComplex F (up ℤ) 0).app (𝟙_ C)).symm

section Total

variable (K L : CochainComplex C ℤ)
variable [HomologicalComplex.HasTensor K L]
variable [HomologicalComplex.HasTensor
  ((map F).obj K) ((map F).obj L)]
variable [(mappedTensorBicomplex F K L).HasTotal (up ℤ)]

/-- The canonical tensor comparison for the termwise action of a lax monoidal additive functor.
It is the totalization of the pointwise tensorator followed by the additive-functor/total
comparison. -/
@[stacks 07A4 "cochain-complex tensor comparison"]
noncomputable def tensorComparison :
    HomologicalComplex.tensorObj
        ((map F).obj K) ((map F).obj L) ⟶
      (map F).obj (HomologicalComplex.tensorObj K L) :=
  (HomologicalComplex₂.total.mapIso (tensorBicomplexIso F K L) (up ℤ)).hom ≫
    HomologicalComplex₂.Total.Map.Comparison.hom F (tensorBicomplex K L) (up ℤ)

/-- On the `(p, q)` summand, the cochain-complex tensor comparison is the base tensorator followed
by the image under `F` of the original inclusion into the total tensor complex. -/
@[reassoc]
theorem ι_tensorComparison (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj
        ((map F).obj K) ((map F).obj L) p q n h ≫
        (tensorComparison F K L).f n =
      LaxMonoidal.μ F (K.X p) (L.X q) ≫
        F.map (HomologicalComplex.ιTensorObj K L p q n h) := sorry

/-- The exact preservation condition needed for the tensor comparison on `K` and `L`: `F`
preserves the coproduct defining every total degree of their pointwise tensor bicomplex. -/
@[stacks 07A4 "tensor-total coproduct preservation"]
abbrev PreservesTensorTotal : Prop :=
  HomologicalComplex₂.Total.Map.Comparison.PreservesTotalDegreeCoproducts
    F (tensorBicomplex K L) (up ℤ)

/-- The cochain-complex tensor comparison is invertible when `F` preserves precisely the
coproducts used by the total tensor complex. -/
@[stacks 07A4 "invertible cochain-complex tensor comparison"]
theorem tensorComparison_isIso [PreservesTensorTotal F K L] :
    IsIso (tensorComparison F K L) := sorry

/-- Preservation of all colimits of the relevant size is a convenient sufficient condition for
invertibility of the cochain-complex tensor comparison. -/
theorem tensorComparison_isIso_of_preservesColimits
    [PreservesColimitsOfSize.{0, 0} F] :
    IsIso (tensorComparison F K L) := sorry

end Total

section Naturality

variable {K K' L L' : CochainComplex C ℤ}
variable [HomologicalComplex.HasTensor K L] [HomologicalComplex.HasTensor K' L']
variable [HomologicalComplex.HasTensor
  ((map F).obj K) ((map F).obj L)]
variable [HomologicalComplex.HasTensor
  ((map F).obj K') ((map F).obj L')]
variable [(mappedTensorBicomplex F K L).HasTotal (up ℤ)]
variable [(mappedTensorBicomplex F K' L').HasTotal (up ℤ)]

/-- The tensor comparison is natural simultaneously in both cochain-complex variables. -/
@[reassoc]
theorem tensorComparison_natural (f : K ⟶ K') (g : L ⟶ L') :
    HomologicalComplex.tensorHom
        ((map F).map f) ((map F).map g) ≫
        tensorComparison F K' L' =
      tensorComparison F K L ≫
        (map F).map (HomologicalComplex.tensorHom f g) := sorry

end Naturality

/-- Every termwise image of a pointwise tensor bicomplex admits the unbounded totalization used
by `tensorComparison`.  This condition concerns existence in the target category, not preservation
by `F`. -/
abbrev HasMappedTensorTotals : Prop :=
  ∀ K L : CochainComplex C ℤ, (mappedTensorBicomplex F K L).HasTotal (up ℤ)

section Monoidal

variable [∀ G₁ G₂ : GradedObject ℤ C, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ C,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ C,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [∀ G₁ G₂ : GradedObject ℤ D, GradedObject.HasTensor G₁ G₂]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ D,
  GradedObject.HasGoodTensor₁₂Tensor G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ : GradedObject ℤ D,
  GradedObject.HasGoodTensorTensor₂₃ G₁ G₂ G₃]
variable [∀ G₁ G₂ G₃ G₄ : GradedObject ℤ D,
  GradedObject.HasTensor₄ObjExt G₁ G₂ G₃ G₄]
variable [HasMappedTensorTotals F]

/-- In the canonical totalized monoidal structures, the raw `tensorHom` naturality theorem is the
usual naturality square written with `⊗ₘ`. -/
@[reassoc]
theorem tensorComparison_naturality {K K' L L' : CochainComplex C ℤ}
    (f : K ⟶ K') (g : L ⟶ L') :
    ((map F).map f ⊗ₘ (map F).map g) ≫ tensorComparison F K' L' =
      tensorComparison F K L ≫ (map F).map (f ⊗ₘ g) := sorry

/-- Naturality of the tensor comparison in its left variable, in whiskering form. -/
theorem tensorComparison_natural_left {K K' : CochainComplex C ℤ}
    (f : K ⟶ K') (L : CochainComplex C ℤ) :
    (map F).map f ▷ (map F).obj L ≫ tensorComparison F K' L =
      tensorComparison F K L ≫ (map F).map (f ▷ L) := sorry

/-- Naturality of the tensor comparison in its right variable, in whiskering form. -/
theorem tensorComparison_natural_right (K : CochainComplex C ℤ)
    {L L' : CochainComplex C ℤ} (g : L ⟶ L') :
    (map F).obj K ◁ (map F).map g ≫ tensorComparison F K L' =
      tensorComparison F K L ≫ (map F).map (K ◁ g) := sorry

/-- For a fixed left factor, the tensor comparisons form a natural transformation in the right
cochain-complex variable. -/
noncomputable def tensorComparisonApp (K : CochainComplex C ℤ) :
    (curriedTensorPre (map F)).obj K ⟶ (curriedTensorPost (map F)).obj K where
  app L := tensorComparison F K L
  naturality {_ _} g := tensorComparison_natural_right F K g

/-- The right-variable tensor-comparison transformations are natural in the left variable. -/
theorem tensorComparisonApp_natural {K K' : CochainComplex C ℤ} (f : K ⟶ K') :
    (curriedTensorPre (map F)).map f ≫ tensorComparisonApp F K' =
      tensorComparisonApp F K ≫ (curriedTensorPost (map F)).map f := sorry

/-- The canonical tensor comparison as a natural transformation of bifunctors. -/
@[stacks 07A4 "cochain-complex tensor comparison transformation"]
noncomputable def tensorComparisonNatTrans :
    curriedTensorPre (map F) ⟶ curriedTensorPost (map F) where
  app K := tensorComparisonApp F K
  naturality {_ _} f := tensorComparisonApp_natural F f

/-- The cochain-complex tensor comparison respects the canonical totalized associators. -/
theorem tensorComparison_associativity (K L M : CochainComplex C ℤ) :
    (tensorComparison F K L ⊗ₘ 𝟙 ((map F).obj M)) ≫
        tensorComparison F (K ⊗ L) M ≫ (map F).map (α_ K L M).hom =
      (α_ ((map F).obj K) ((map F).obj L) ((map F).obj M)).hom ≫
        (𝟙 ((map F).obj K) ⊗ₘ tensorComparison F L M) ≫
          tensorComparison F K (L ⊗ M) := sorry

/-- The cochain-complex unit and tensor comparisons respect the canonical left unitor. -/
theorem tensorComparison_left_unitality (K : CochainComplex C ℤ) :
    (λ_ ((map F).obj K)).hom =
      ((unitIso F).hom ⊗ₘ 𝟙 ((map F).obj K)) ≫
        tensorComparison F (𝟙_ (CochainComplex C ℤ)) K ≫
          (map F).map (λ_ K).hom := sorry

/-- The cochain-complex unit and tensor comparisons respect the canonical right unitor. -/
theorem tensorComparison_right_unitality (K : CochainComplex C ℤ) :
    (ρ_ ((map F).obj K)).hom =
      (𝟙 ((map F).obj K) ⊗ₘ (unitIso F).hom) ≫
        tensorComparison F K (𝟙_ (CochainComplex C ℤ)) ≫
          (map F).map (ρ_ K).hom := sorry

/-- Applying a monoidal additive functor termwise to cochain complexes is canonically lax
monoidal, without assuming that it preserves the coproducts used by totalization. -/
@[stacks 07A4 "termwise cochain-complex lax monoidal functor"]
noncomputable instance laxMonoidal : (map F).LaxMonoidal :=
  Functor.LaxMonoidal.ofTensorHom
    (unitIso F).hom (fun K L ↦ tensorComparison F K L)
    (tensorComparison_naturality F) (tensorComparison_associativity F)
    (tensorComparison_left_unitality F) (tensorComparison_right_unitality F)

section Strong

variable [∀ K L : CochainComplex C ℤ, IsIso (tensorComparison F K L)]

/-- The conditional strong monoidal core of the termwise cochain-complex functor.  Its inverse
tensorators come only from the caller-supplied `IsIso` instances. -/
@[stacks 07A4 "termwise cochain-complex monoidal core"]
noncomputable def coreMonoidal : (map F).CoreMonoidal :=
  { εIso := unitIso F
    μIso := fun K L ↦ asIso (tensorComparison F K L)
    μIso_hom_natural_left := tensorComparison_natural_left F
    μIso_hom_natural_right := fun K f ↦ tensorComparison_natural_right F K f
    associativity := tensorComparison_associativity F
    left_unitality := tensorComparison_left_unitality F
    right_unitality := tensorComparison_right_unitality F }

/-- The strong monoidal structure on the termwise cochain-complex functor, conditional on the
canonical tensor comparisons being invertible. -/
@[stacks 07A4 "termwise cochain-complex monoidal functor"]
noncomputable instance monoidal : (map F).Monoidal :=
  (coreMonoidal F).toMonoidal

end Strong

end Monoidal

end CategoryTheory.Functor.Cochain
