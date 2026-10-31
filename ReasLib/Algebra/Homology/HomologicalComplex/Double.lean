/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.Double
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import ReasLib.CategoryTheory.Homology.DegreewiseSplit
public import ReasLib.CategoryTheory.ShortComplex.FunctorCategory
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functorial two-term homological complexes

Mathlib's `HomologicalComplex.double` places a morphism in two adjacent degrees. This file
packages that construction functorially on the arrow category, together with its canonical
single--double--single row and an explicit splitting of that row in every degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe v u w

namespace HomologicalComplex.double

section Functorial

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
variable {I : Type w} {c : ComplexShape I} {i₀ i₁ : I}

namespace map

/-- The two endpoint maps of a square commute with the differential in the target double
complex. -/
theorem comm {f g : Arrow C} (φ : f ⟶ g) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) :
    (φ.left ≫ (doubleXIso₀ g.hom hi).inv) ≫ (double g.hom hi).d i₀ i₁ =
      f.hom ≫
        (φ.right ≫
          (doubleXIso₁ g.hom hi hne).inv) := by
  simp [double_d _ _ hne, Category.assoc]

/-- The target endpoint map of a square commutes with every outgoing zero differential of the
target double complex. -/
theorem next {f g : Arrow C} (φ : f ⟶ g) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) (j : I) (hj : c.Rel i₁ j) :
    (φ.right ≫ (doubleXIso₁ g.hom hi hne).inv) ≫
      (double g.hom hi).d i₁ j = 0 := by
  rw [double_d_eq_zero₀ _ _ _ _ hne.symm, comp_zero]

end map

/-- A commutative square induces the corresponding map between two-term complexes. -/
@[stacks 0192 "functorial map of two-term complexes"]
noncomputable def map {f g : Arrow C} (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (φ : f ⟶ g) :
    double f.hom hi ⟶ double g.hom hi :=
  mkHomFromDouble hi hne
    (φ.left ≫ (doubleXIso₀ g.hom hi).inv)
    (φ.right ≫ (doubleXIso₁ g.hom hi hne).inv)
    (map.comm φ hi hne) (map.next φ hi hne)

namespace map

/-- At the source degree, `double.map` is the left side of the defining square under the
canonical endpoint identifications. -/
@[simp, stacks 0192 "source component of a map of two-term complexes"]
theorem f₀ {f g : Arrow C} (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (φ : f ⟶ g) :
    (map hi hne φ).f i₀ =
      (doubleXIso₀ f.hom hi).hom ≫ φ.left ≫ (doubleXIso₀ g.hom hi).inv := by
  simp [HomologicalComplex.double.map]

/-- At the target degree, `double.map` is the right side of the defining square under the
canonical endpoint identifications. -/
@[simp, stacks 0192 "target component of a map of two-term complexes"]
theorem f₁ {f g : Arrow C} (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    (φ : f ⟶ g) :
    (map hi hne φ).f i₁ =
      (doubleXIso₁ f.hom hi hne).hom ≫ φ.right ≫
        (doubleXIso₁ g.hom hi hne).inv := by
  simp [HomologicalComplex.double.map]

/-- The map of double complexes associated to an identity square is the identity. -/
theorem id (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (f : Arrow C) :
    map hi hne (𝟙 f) = 𝟙 (double f.hom hi) := by
  apply from_double_hom_ext
  · simp
  · simp

/-- Maps of double complexes preserve composition of commutative squares. -/
theorem comp (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) {f g h : Arrow C}
    (φ : f ⟶ g) (ψ : g ⟶ h) :
    map hi hne (φ ≫ ψ) = map hi hne φ ≫ map hi hne ψ := by
  apply from_double_hom_ext
  · simp [Category.assoc]
  · simp [Category.assoc]

end map

/-- Placing an arrow in two adjacent degrees defines a functor from the arrow category. -/
@[stacks 0192 "two-term complex functor on the arrow category"]
noncomputable def functor (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] {I : Type w} {c : ComplexShape I} {i₀ i₁ : I}
    (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) : Arrow C ⥤ HomologicalComplex C c where
  obj f := double f.hom hi
  map φ := map hi hne φ
  map_id f := map.id hi hne f
  map_comp φ ψ := map.comp hi hne φ ψ

/-- The value of `double.functor` is Mathlib's two-term complex. -/
@[simp, stacks 0192 "two-term complex functor object formula"]
theorem functor_obj (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (f : Arrow C) :
    (functor C hi hne).obj f = double f.hom hi := rfl

/-- The action of `double.functor` on a square is `double.map`. -/
@[simp, stacks 0192 "two-term complex functor map formula"]
theorem functor_map (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁)
    {f g : Arrow C} (φ : f ⟶ g) :
    (functor C hi hne).map φ = map hi hne φ := rfl

section Cokernel

variable [DecidableEq I] [HasCokernels C]

/-- The differential into the target of a two-term complex vanishes after the cokernel
projection. -/
@[stacks 0192 "two-term complex cokernel augmentation relation"]
theorem toCokernelApp_comm (f : Arrow C) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) (i : I) (h : c.Rel i i₁) :
    (double f.hom hi).d i i₁ ≫
        ((doubleXIso₁ f.hom hi hne).hom ≫ cokernel.π f.hom) = 0 := by
  obtain rfl := c.prev_eq h hi
  simp [double_d _ _ hne, Category.assoc]

/-- The canonical map from a two-term complex to its cokernel concentrated in the target
degree. -/
@[stacks 0192 "two-term complex cokernel augmentation"]
noncomputable def toCokernelApp (f : Arrow C) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) :
    double f.hom hi ⟶ (single C c i₁).obj (cokernel f.hom) :=
  mkHomToSingle ((doubleXIso₁ f.hom hi hne).hom ≫ cokernel.π f.hom)
    (toCokernelApp_comm f hi hne)

/-- Cokernel augmentations of two-term complexes are natural in commutative squares. -/
@[stacks 0192 "naturality of the two-term cokernel augmentation"]
theorem toCokernelApp_naturality {f g : Arrow C} (φ : f ⟶ g)
    (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    map hi hne φ ≫ toCokernelApp g hi hne =
      toCokernelApp f hi hne ≫ (single C c i₁).map ((Limits.coker C).map φ) := by
  apply to_single_hom_ext
  change (map hi hne φ).f i₁ ≫ (toCokernelApp g hi hne).f i₁ =
    (toCokernelApp f hi hne).f i₁ ≫
      ((single C c i₁).map ((Limits.coker C).map φ)).f i₁
  simp [toCokernelApp, single_map_f_self, Category.assoc, Limits.coker]

/-- The natural transformation from the two-term-complex functor to the target-degree
cokernel functor. -/
@[stacks 0192 "functorial two-term cokernel augmentation"]
noncomputable def toCokernel (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] [HasCokernels C] {I : Type w} [DecidableEq I]
    {c : ComplexShape I} {i₀ i₁ : I} (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    functor C hi hne ⟶ Limits.coker C ⋙ single C c i₁ where
  app f := toCokernelApp f hi hne
  naturality _ _ φ := toCokernelApp_naturality φ hi hne

/-- A component of `toCokernel` is the canonical cokernel augmentation. -/
@[simp, stacks 0192 "component of the functorial two-term cokernel augmentation"]
theorem toCokernel_app (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (f : Arrow C) :
    (toCokernel C hi hne).app f = toCokernelApp f hi hne := rfl

end Cokernel

namespace ιApp

/-- The endpoint inclusion into a two-term complex commutes with every outgoing differential. -/
theorem comm (f : Arrow C) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) (j : I) (hj : c.Rel i₁ j) :
    (doubleXIso₁ f.hom hi hne).inv ≫
      (double f.hom hi).d i₁ j = 0 := by
  rw [double_d_eq_zero₀ _ _ _ _ hne.symm, comp_zero]

end ιApp

namespace πApp

/-- The endpoint projection from a two-term complex commutes with every incoming differential. -/
theorem comm (f : Arrow C) (hi : c.Rel i₀ i₁)
    (j : I) (hj : c.Rel j i₀) :
    (double f.hom hi).d j i₀ ≫ (doubleXIso₀ f.hom hi).hom = 0 := by
  classical
  by_cases h : i₀ = i₁
  · subst i₁
    simp [HomologicalComplex.double]
    rfl
  · rw [double_d_eq_zero₁ _ _ _ _ h, zero_comp]

end πApp

section Endpoints

variable [DecidableEq I]

/-- The canonical inclusion of the target endpoint, concentrated in degree `i₁`, into a
two-term complex. -/
@[stacks 0192 "target endpoint inclusion into a two-term complex"]
noncomputable def ιApp (f : Arrow C) (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    (single C c i₁).obj f.right ⟶ double f.hom hi :=
  mkHomFromSingle
    (doubleXIso₁ f.hom hi hne).inv
    (ιApp.comm f hi hne)

namespace ι

/-- Endpoint inclusions are natural in commutative squares. -/
theorem naturality {f g : Arrow C} (φ : f ⟶ g) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) :
    ((Arrow.rightFunc : Arrow C ⥤ C) ⋙ single C c i₁).map φ ≫ ιApp g hi hne =
      ιApp f hi hne ≫ (functor C hi hne).map φ := by
  apply from_single_hom_ext
  change ((single C c i₁).map φ.right).f i₁ ≫ (ιApp g hi hne).f i₁ =
    (ιApp f hi hne).f i₁ ≫ (map hi hne φ).f i₁
  simp [ιApp, single_map_f_self, Category.assoc]

end ι

/-- The target-endpoint inclusions form a natural transformation into the two-term-complex
functor. -/
@[stacks 0192 "natural target endpoint inclusion into two-term complexes"]
noncomputable def ι (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] {I : Type w} {c : ComplexShape I} {i₀ i₁ : I}
    [DecidableEq I] (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    (Arrow.rightFunc : Arrow C ⥤ C) ⋙ single C c i₁ ⟶ functor C hi hne where
  app f := ιApp f hi hne
  naturality _ _ φ := ι.naturality φ hi hne

/-- The component of the natural endpoint inclusion is `ιApp`. -/
@[simp, stacks 0192 "target endpoint inclusion component formula"]
theorem ι_app (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (f : Arrow C) :
    (ι C hi hne).app f = ιApp f hi hne := rfl

/-- The canonical projection from a two-term complex onto its source endpoint, concentrated in
degree `i₀`. -/
@[stacks 0192 "source endpoint projection from a two-term complex"]
noncomputable def πApp (f : Arrow C) (hi : c.Rel i₀ i₁) :
    double f.hom hi ⟶ (single C c i₀).obj f.left :=
  mkHomToSingle (doubleXIso₀ f.hom hi).hom (πApp.comm f hi)

namespace π

/-- Endpoint projections are natural in commutative squares. -/
theorem naturality {f g : Arrow C} (φ : f ⟶ g) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) :
    (functor C hi hne).map φ ≫ πApp g hi =
      πApp f hi ≫ ((Arrow.leftFunc : Arrow C ⥤ C) ⋙ single C c i₀).map φ := by
  apply to_single_hom_ext
  change (map hi hne φ).f i₀ ≫ (πApp g hi).f i₀ =
    (πApp f hi).f i₀ ≫ ((single C c i₀).map φ.left).f i₀
  simp [πApp, single_map_f_self, Category.assoc]

end π

/-- The source-endpoint projections form a natural transformation out of the two-term-complex
functor. -/
@[stacks 0192 "natural source endpoint projection from two-term complexes"]
noncomputable def π (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] {I : Type w} {c : ComplexShape I} {i₀ i₁ : I}
    [DecidableEq I] (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    functor C hi hne ⟶ (Arrow.leftFunc : Arrow C ⥤ C) ⋙ single C c i₀ where
  app f := πApp f hi
  naturality _ _ φ := π.naturality φ hi hne

/-- The component of the natural endpoint projection is `πApp`. -/
@[simp, stacks 0192 "source endpoint projection component formula"]
theorem π_app (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (f : Arrow C) :
    (π C hi hne).app f = πApp f hi := rfl

/-- The natural endpoint inclusion and projection compose to zero. -/
@[stacks 0192 "single-double-single composition"]
theorem ι_comp_π (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    ι C hi hne ≫ π C hi hne = 0 := by
  apply NatTrans.ext
  funext f
  apply from_single_hom_ext
  exact (isZero_single_obj_X c i₀ f.left i₁ hne.symm).eq_of_tgt _ _

/-- The canonical single--double--single short complex, functorial in the underlying arrow. -/
@[stacks 0192 "functorial single-double-single short complex"]
noncomputable def shortComplex (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [HasZeroObject C] {I : Type w} {c : ComplexShape I} {i₀ i₁ : I}
    [DecidableEq I] (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    ShortComplex (Arrow C ⥤ HomologicalComplex C c) :=
  ShortComplex.mk (ι C hi hne) (π C hi hne) (ι_comp_π hi hne)

namespace shortComplex

/-- Evaluate the functorial single--double--single row at an arrow. -/
@[stacks 0192 "single-double-single short complex at an arrow"]
abbrev app {C : Type u} [Category.{v} C] [HasZeroMorphisms C] [HasZeroObject C]
    {I : Type w} {c : ComplexShape I} {i₀ i₁ : I} [DecidableEq I]
    (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (f : Arrow C) :
    ShortComplex (HomologicalComplex C c) :=
  ShortComplex.FunctorCategory.app (shortComplex C hi hne) f

end shortComplex

end Endpoints

end Functorial

section Splitting

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {I : Type w} {c : ComplexShape I} {i₀ i₁ : I} [DecidableEq I]

namespace degree

/-- In degree `n`, retract the middle two-term complex onto the target-endpoint single
complex. -/
@[stacks 0192 "degreewise retraction of the single-double-single row"]
noncomputable def retraction (f : Arrow C) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) (n : I) :
    (double f.hom hi).X n ⟶ ((single C c i₁).obj f.right).X n :=
  if h : n = i₁ then
    ((double f.hom hi).XIsoOfEq h).hom ≫
      (doubleXIso₁ f.hom hi hne).hom ≫
        (singleObjXIsoOfEq c i₁ f.right n h).inv
  else 0

/-- In degree `n`, include the source-endpoint single complex as a section of the endpoint
projection. -/
@[stacks 0192 "degreewise section of the single-double-single row"]
noncomputable def section_ (f : Arrow C) (hi : c.Rel i₀ i₁) (n : I) :
    ((single C c i₀).obj f.left).X n ⟶ (double f.hom hi).X n :=
  if h : n = i₀ then
    (singleObjXIsoOfEq c i₀ f.left n h).hom ≫
      (doubleXIso₀ f.hom hi).inv ≫ ((double f.hom hi).XIsoOfEq h).inv
  else 0

namespace laws

/-- The degreewise retraction is a right inverse to the endpoint inclusion. -/
theorem f_r (f : Arrow C) (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (n : I) :
    ((shortComplex.app hi hne f).degreewise n).f ≫
      retraction f hi hne n = 𝟙 _ := by
  by_cases h : n = i₁
  · subst n
    change (ιApp f hi hne).f i₁ ≫ retraction f hi hne i₁ = 𝟙 _
    simp [ιApp, retraction, singleObjXSelf, Category.assoc]
  · exact (isZero_single_obj_X c i₁ f.right n h).eq_of_src _ _

/-- The degreewise section is a left inverse to the endpoint projection. -/
theorem s_g (f : Arrow C) (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (n : I) :
    section_ f hi n ≫ ((shortComplex.app hi hne f).degreewise n).g = 𝟙 _ := by
  by_cases h : n = i₀
  · subst n
    change section_ f hi i₀ ≫ (πApp f hi).f i₀ = 𝟙 _
    simp [πApp, section_, singleObjXSelf, Category.assoc]
  · exact (isZero_single_obj_X c i₀ f.left n h).eq_of_src _ _

/-- The retraction and section split the identity of the middle term in every degree. -/
theorem id (f : Arrow C) (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) (n : I) :
    (retraction f hi hne n ≫
        (((shortComplex.app hi hne f).degreewise n).f :
          ((single C c i₁).obj f.right).X n ⟶ (double f.hom hi).X n) :
        (double f.hom hi).X n ⟶ (double f.hom hi).X n) +
      ((((shortComplex.app hi hne f).degreewise n).g :
          (double f.hom hi).X n ⟶ ((single C c i₀).obj f.left).X n) ≫
        section_ f hi n :
        (double f.hom hi).X n ⟶ (double f.hom hi).X n) = 𝟙 _ := by
  change retraction f hi hne n ≫ (ιApp f hi hne).f n +
    (πApp f hi).f n ≫ section_ f hi n = 𝟙 _
  by_cases h₀ : n = i₀
  · subst n
    simp [retraction, section_, πApp, hne, singleObjXSelf, Category.assoc]
  · by_cases h₁ : n = i₁
    · subst n
      simp [retraction, section_, ιApp, h₀, singleObjXSelf, Category.assoc]
    · exact (isZero_double_X f.hom hi n h₀ h₁).eq_of_src _ _

end laws

/-- The explicit splitting of the single--double--single row in degree `n`. -/
@[stacks 0192 "degreewise splitting of the single-double-single row"]
noncomputable def splitting (f : Arrow C) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) (n : I) :
    ((shortComplex.app hi hne f).degreewise n).Splitting where
  r := retraction f hi hne n
  s := section_ f hi n
  f_r := laws.f_r f hi hne n
  s_g := laws.s_g f hi hne n
  id := laws.id f hi hne n

end degree

/-- The chosen family of splittings of the single--double--single row associated to an arrow. -/
@[stacks 0192 "chosen degreewise splitting of the single-double-single row"]
noncomputable def degreewiseSplitting (f : Arrow C) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) :
    ShortComplex.DegreewiseSplitting (shortComplex.app hi hne f) :=
  fun n ↦ degree.splitting f hi hne n

/-- The single--double--single row associated to an arrow is degreewise split. -/
@[stacks 0192 "degreewise-split single-double-single row"]
theorem isDegreewiseSplit (f : Arrow C) (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    (shortComplex.app hi hne f).IsDegreewiseSplit := by
  intro n
  exact ⟨degree.splitting f hi hne n⟩

end Splitting

section ShortExact

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {I : Type w} {c : ComplexShape I} {i₀ i₁ : I} [DecidableEq I]

/-- The single--double--single row of an arrow is short exact. -/
@[stacks 0192 "short exact single-double-single row"]
theorem shortComplex.app.shortExact (f : Arrow C) (hi : c.Rel i₀ i₁)
    (hne : i₀ ≠ i₁) :
    (shortComplex.app hi hne f).ShortExact := by
  apply shortExact_of_degreewise_shortExact
  intro n
  exact (degree.splitting f hi hne n).shortExact

end ShortExact

section Acyclic

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
variable {I : Type w} {c : ComplexShape I} {i₀ i₁ : I}

/-- A two-term complex whose unique nonzero differential is an isomorphism is acyclic. -/
@[stacks 0192 "acyclic two-term complex with invertible differential"]
theorem acyclic_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f]
    (hi : c.Rel i₀ i₁) (hne : i₀ ≠ i₁) :
    (double f hi).Acyclic := by
  intro n
  by_cases h₀ : n = i₀
  · subst n
    haveI : IsIso ((double f hi).sc i₀).g := by
      change IsIso ((double f hi).d i₀ (c.next i₀))
      rw [c.next_eq' hi, double_d f hi hne]
      infer_instance
    exact (ShortComplex.exact_iff_mono ((double f hi).sc i₀)
      (double_d_eq_zero₁ f hi _ _ hne)).2 inferInstance
  · by_cases h₁ : n = i₁
    · subst n
      haveI : IsIso ((double f hi).sc i₁).f := by
        change IsIso ((double f hi).d (c.prev i₁) i₁)
        rw [c.prev_eq' hi, double_d f hi hne]
        infer_instance
      exact (ShortComplex.exact_iff_epi ((double f hi).sc i₁)
        (double_d_eq_zero₀ f hi _ _ hne.symm)).2 inferInstance
    · exact ExactAt.of_isZero (isZero_double_X f hi n h₀ h₁)

end Acyclic

end HomologicalComplex.double
