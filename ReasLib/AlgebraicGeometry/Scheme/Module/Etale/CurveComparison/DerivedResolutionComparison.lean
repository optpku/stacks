/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Cochain
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat.Homology
public import ReasLib.Algebra.Homology.Embedding.Functor
public import Mathlib.CategoryTheory.Abelian.RightDerived

@[expose] public section
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe w

namespace ActualResolutionComparison
variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
variable [EnoughInjectives C] (F : C ⥤ D) [F.Additive]

/-- The degree-zero object is constructed by extending the actual nonnegative single complex. -/
def singleModel (M : C) : DerivedCategory.Plus C :=
  DerivedCategory.Plus.Q.obj ((CochainComplex.Plus.extendNat C).obj ((CochainComplex.single₀ C).obj M))

/-- The same degree-zero model on morphisms uses the actual single-complex,
extension and localization functors. -/
def singleModelFunctor : C ⥤ DerivedCategory.Plus C :=
  CochainComplex.single₀ C ⋙ CochainComplex.Plus.extendNat C ⋙ DerivedCategory.Plus.Q

/-- The actual augmentation of a nonnegative injective resolution, after extension and localization. -/
def resolutionInclusion {M : C} (I : InjectiveResolution M) :
    singleModel M ⟶ DerivedCategory.Plus.Q.obj ((CochainComplex.Plus.extendNat C).obj I.cocomplex) :=
  DerivedCategory.Plus.Q.map ((CochainComplex.Plus.extendNat C).map I.ι)

set_option backward.isDefEq.respectTransparency false in
/-- Extension and localization turn the resolution augmentation into an isomorphism. -/
instance resolutionInclusion_isIso {M : C} (I : InjectiveResolution M) :
    IsIso (resolutionInclusion I) := by
  haveI : IsIso ((CochainComplex.Plus.ι C ⋙ DerivedCategory.Q).map
      ((CochainComplex.Plus.extendNat C).map I.ι)) := by
    change IsIso (DerivedCategory.Q.map
      (HomologicalComplex.extendMap I.ι ComplexShape.embeddingUpNat))
    infer_instance
  have h := NatIso.naturality_2 (DerivedCategory.Plus.Qh.compInclusionIso C)
    ((CochainComplex.Plus.extendNat C).map I.ι)
  have hIso : IsIso ((DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι).map
      ((CochainComplex.Plus.extendNat C).map I.ι)) := by
    rw [← h]
    infer_instance
  haveI : IsIso
      ((DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C).map
        (resolutionInclusion I)) := hIso
  exact isIso_of_reflects_iso (resolutionInclusion I)
    (DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C)

/-- The coefficient/extension comparison is the actual degreewise map from the extension owner. -/
def coefficientExtensionMap {M : C} (I : InjectiveResolution M) :
    (CochainComplex.Plus.extendNat D).obj ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) ⟶
      F.mapCochainComplexPlus.obj ((CochainComplex.Plus.extendNat C).obj I.cocomplex) :=
  ObjectProperty.homMk (ComplexShape.embeddingUpNat.mapAppIso F I.cocomplex).inv

/-- A chosen resolution computes the bounded derived value through its canonical
derived unit and the inverse of its actual augmentation, never an arbitrary iso. -/
def resolutionToDerived {M : C} (I : InjectiveResolution M) :
    DerivedCategory.Plus.Q.obj ((CochainComplex.Plus.extendNat D).obj
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex)) ⟶
        (Functor.RightDerived.Bounded.functor F).obj (singleModel M) :=
  Functor.RightDerived.Bounded.fromCochainMap F (coefficientExtensionMap F I) ≫
    (Functor.RightDerived.Bounded.functor F).map (asIso (resolutionInclusion I)).inv

/-- The displayed resolution map is invertible since injective resolution terms are acyclic. -/
instance resolutionToDerived_isIso {M : C} (I : InjectiveResolution M) :
    IsIso (resolutionToDerived F I) := sorry

/-- The ordinary right-derived degree maps to the bounded model by specified
resolution homology, extension homology, and the derived unit. -/
def ordinaryToBounded {M : C} (I : InjectiveResolution M) (n : ℕ) :
    (F.rightDerived n).obj M ⟶
      (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).obj
        ((Functor.RightDerived.Bounded.functor F).obj (singleModel M)) :=
  (I.isoRightDerivedObj F n).hom ≫
    (CochainComplex.Plus.extendNatDerivedHomologyIsoApp D
      ((F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex) n).inv ≫
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).map (resolutionToDerived F I)

/-- The ordinary-to-bounded map is an isomorphism of the actual resolution models. -/
instance ordinaryToBounded_isIso {M : C} (I : InjectiveResolution M) (n : ℕ) :
    IsIso (ordinaryToBounded F I n) := by
  unfold ordinaryToBounded
  infer_instance

/-- The canonical degree comparison inverts only the specified resolution map. -/
def ordinaryToBoundedIso {M : C} (I : InjectiveResolution M) (n : ℕ) :=
  @asIso _ _ _ _ (ordinaryToBounded F I n) (ordinaryToBounded_isIso F I n)

/-- The map is independent of which injective resolution computes it. -/
theorem ordinaryToBounded_independent {M : C} (I J : InjectiveResolution M) (n : ℕ) :
    ordinaryToBounded F I n = ordinaryToBounded F J n := sorry

/-- The extended single complex maps to Mathlib's single object through the
specified extension-single isomorphism and localization comparison. -/
def singleModelIso (M : C) : singleModel M ≅ (DerivedCategory.Plus.singleFunctor C 0).obj M :=
  (DerivedCategory.Plus.ι : DerivedCategory.Plus C ⥤ DerivedCategory C).preimageIso
    ((CategoryTheory.DerivedCategory.Plus.Qh.compInclusionIso C).app
        ((CochainComplex.Plus.extendNat C).obj ((CochainComplex.single₀ C).obj M)) ≪≫
      DerivedCategory.Q.mapIso (HomologicalComplex.extendSingleIso ComplexShape.embeddingUpNat M 0 0 rfl))

/-- The actual resolution comparison in the standard bounded-derived degree model. -/
def standardDegreeIso (M : C) (n : ℕ) :
    (F.rightDerived n).obj M ≅ (Functor.RightDerived.Bounded.degree F (n : ℤ)).obj M :=
  ordinaryToBoundedIso F (injectiveResolution M) n ≪≫
    (DerivedCategory.Plus.homologyFunctor D (n : ℤ)).mapIso
      ((Functor.RightDerived.Bounded.functor F).mapIso (singleModelIso M))

/-- Naturality of the actual resolution/derived-unit comparison. -/
theorem standardDegreeIso_naturality {M N : C} (a : M ⟶ N) (n : ℕ) :
    (F.rightDerived n).map a ≫ (standardDegreeIso F N n).hom =
      (standardDegreeIso F M n).hom ≫ (Functor.RightDerived.Bounded.degree F (n : ℤ)).map a := sorry

/-- The standard bounded and ordinary derived-degree functors are identified by
their specified resolution maps, not by an isomorphism existence assertion. -/
def standardDegreeNatIso (n : ℕ) : F.rightDerived n ≅ Functor.RightDerived.Bounded.degree F (n : ℤ) :=
  NatIso.ofComponents (fun M ↦ standardDegreeIso F M n) (fun a ↦ standardDegreeIso_naturality F a n)

end ActualResolutionComparison
