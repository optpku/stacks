/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.Monoidal

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Functor.Monoidal CategoryTheory.MonoidalCategory TensorProduct

universe u v

namespace ModuleCat

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B]

/-- Extension of scalars along `φ : A →+* B` preserves finite presentation of modules. -/
theorem extendScalars_isFinitePresentation (φ : A →+* B)
    (M : ModuleCat.{max u v} A)
    (hM : isFinitePresentation.{u, max u v} A M) :
    isFinitePresentation.{v, max u v} B ((extendScalars φ).obj M) := by
  letI : Algebra A B := φ.toAlgebra
  letI : Module.FinitePresentation A M := hM
  change Module.FinitePresentation B (B ⊗[A] M)
  infer_instance

/-- Restriction of extension of scalars to finitely presented modules. -/
noncomputable def fpExtendScalars (φ : A →+* B) :
    (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory :=
  (isFinitePresentation.{v, max u v} B).lift
    ((isFinitePresentation.{u, max u v} A).ι ⋙ extendScalars φ) fun X ↦
    extendScalars_isFinitePresentation φ X.obj X.property

/-- The unit comparison for extension of scalars on the tensor unit. -/
noncomputable def fpExtendScalars.εLinearEquiv (φ : A →+* B) :
    ULift.{u, v} B ≃ₗ[B] (extendScalars φ).obj (of A (ULift.{v, u} A)) :=
  -- Local instance justification (noncanonical choice): φ selects the algebra structure required by the tensor-unit comparison API.
  letI : Algebra A B := φ.toAlgebra
  -- Local instance justification (proof-local temporary data): the tensor-unit comparison requires the scalar-tower proof for the B-module restricted along φ.
  letI : IsScalarTower A B ((restrictScalars φ).obj (of B B)) :=
    IsScalarTower.of_algebraMap_smul fun a c => by
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  (ULift.moduleEquiv : ULift.{u, v} B ≃ₗ[B] B).trans <|
    (AlgebraTensorModule.rid A B
        ((restrictScalars φ).obj (of B B))).symm.trans <|
      AlgebraTensorModule.congr
        (LinearEquiv.refl B ((restrictScalars φ).obj (of B B)))
        (ULift.moduleEquiv : ULift.{v, u} A ≃ₗ[A] A).symm

/-- The unit isomorphism for extension of scalars on finitely presented modules. -/
noncomputable def fpExtendScalars.εIsoData (φ : A →+* B) :
    𝟙_ (isFinitePresentation.{v, max u v} B).FullSubcategory ≅
      (fpExtendScalars φ).obj
        (𝟙_ (isFinitePresentation.{u, max u v} A).FullSubcategory) :=
  ObjectProperty.isoMk _ (LinearEquiv.toModuleIso (fpExtendScalars.εLinearEquiv φ))

/-- The tensorator equivalence for extension of scalars on finitely presented modules. -/
noncomputable def fpExtendScalars.μLinearEquiv (φ : A →+* B)
    (X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    ((fpExtendScalars φ).obj X ⊗ (fpExtendScalars φ).obj Y).obj ≃ₗ[B]
      ((fpExtendScalars φ).obj (X ⊗ Y)).obj :=
  -- Local instance justification (noncanonical choice): φ.toAlgebra selects the algebra structure required by AlgebraTensorModule.distribBaseChange.
  letI : Algebra A B := φ.toAlgebra
  (AlgebraTensorModule.distribBaseChange A B X.obj Y.obj).symm

/-- The tensorator isomorphism for extension of scalars on finitely presented modules. -/
noncomputable def fpExtendScalars.μIsoData (φ : A →+* B)
    (X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    (fpExtendScalars φ).obj X ⊗ (fpExtendScalars φ).obj Y ≅
      (fpExtendScalars φ).obj (X ⊗ Y) :=
  ObjectProperty.isoMk _ (LinearEquiv.toModuleIso (fpExtendScalars.μLinearEquiv φ X Y))

private theorem fpExtendScalars_μ_natural_left (φ : A →+* B)
    {X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory} (f : X ⟶ Y)
    (Z : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    (fpExtendScalars φ).map f ▷ (fpExtendScalars φ).obj Z ≫
        (fpExtendScalars.μIsoData φ Y Z).hom =
      (fpExtendScalars.μIsoData φ X Z).hom ≫ (fpExtendScalars φ).map (f ▷ Z) := by
  letI : Algebra A B := φ.toAlgebra
  letI : IsScalarTower A B ((restrictScalars φ).obj (of B B)) :=
    IsScalarTower.of_algebraMap_smul fun a c => by
      rw [RingHom.algebraMap_toAlgebra]
      rfl
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  change
    (AlgebraTensorModule.distribBaseChange A B Y.obj Z.obj).symm.toLinearMap ∘ₗ
        (f.hom.hom.baseChange B).rTensor (B ⊗[A] Z.obj) =
      (f.hom.hom.rTensor Z.obj).baseChange B ∘ₗ
        (AlgebraTensorModule.distribBaseChange A B X.obj Z.obj).symm.toLinearMap
  apply TensorProduct.ext
  apply AlgebraTensorModule.ext
  intro b x
  apply AlgebraTensorModule.ext
  intro c z
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, AlgebraTensorModule.distribBaseChange_symm_tmul]

private theorem fpExtendScalars_μ_natural_right (φ : A →+* B)
    {X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory}
    (Z : (isFinitePresentation.{u, max u v} A).FullSubcategory) (f : X ⟶ Y) :
    (fpExtendScalars φ).obj Z ◁ (fpExtendScalars φ).map f ≫
        (fpExtendScalars.μIsoData φ Z Y).hom =
      (fpExtendScalars.μIsoData φ Z X).hom ≫ (fpExtendScalars φ).map (Z ◁ f) := by
  letI : Algebra A B := φ.toAlgebra
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  change
    (AlgebraTensorModule.distribBaseChange A B Z.obj Y.obj).symm.toLinearMap ∘ₗ
        (f.hom.hom.baseChange B).lTensor (B ⊗[A] Z.obj) =
      (f.hom.hom.lTensor Z.obj).baseChange B ∘ₗ
        (AlgebraTensorModule.distribBaseChange A B Z.obj X.obj).symm.toLinearMap
  apply TensorProduct.ext
  apply AlgebraTensorModule.ext
  intro b z
  apply AlgebraTensorModule.ext
  intro c x
  simp only [LinearMap.compr₂ₛₗ_apply, TensorProduct.mk_apply,
    LinearMap.comp_apply, LinearMap.lTensor_tmul, LinearMap.baseChange_tmul,
    LinearEquiv.coe_coe, AlgebraTensorModule.distribBaseChange_symm_tmul]

private theorem fpExtendScalars_associativity (φ : A →+* B)
    (X Y Z : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    (fpExtendScalars.μIsoData φ X Y).hom ▷ (fpExtendScalars φ).obj Z ≫
        (fpExtendScalars.μIsoData φ (X ⊗ Y) Z).hom ≫ (fpExtendScalars φ).map (α_ X Y Z).hom =
      (α_ ((fpExtendScalars φ).obj X) ((fpExtendScalars φ).obj Y)
        ((fpExtendScalars φ).obj Z)).hom ≫
        (fpExtendScalars φ).obj X ◁ (fpExtendScalars.μIsoData φ Y Z).hom ≫
        (fpExtendScalars.μIsoData φ X (Y ⊗ Z)).hom := by
  have h :
      (fpExtendScalars.μIsoData φ (X ⊗ Y) Z).inv ≫
          (fpExtendScalars.μIsoData φ X Y).inv ▷ (fpExtendScalars φ).obj Z ≫
          (α_ ((fpExtendScalars φ).obj X) ((fpExtendScalars φ).obj Y)
            ((fpExtendScalars φ).obj Z)).hom =
        (fpExtendScalars φ).map (α_ X Y Z).hom ≫
          (fpExtendScalars.μIsoData φ X (Y ⊗ Z)).inv ≫
          (fpExtendScalars φ).obj X ◁ (fpExtendScalars.μIsoData φ Y Z).inv := by
    apply ObjectProperty.hom_ext
    apply ((extendRestrictScalarsAdj φ).homEquiv _ _).injective
    apply ModuleCat.hom_ext
    exact TensorProduct.ext_threefold fun x y z => rfl
  rw [← cancel_epi ((fpExtendScalars.μIsoData φ X Y).inv ▷ (fpExtendScalars φ).obj Z),
    ← cancel_epi (fpExtendScalars.μIsoData φ (X ⊗ Y) Z).inv, reassoc_of% h]
  simp only [inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_inv_hom_assoc, Iso.inv_hom_id, Category.comp_id]


private theorem fpExtendScalars_left_unitality (φ : A →+* B)
    (X : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    (λ_ ((fpExtendScalars φ).obj X)).hom =
      (fpExtendScalars.εIsoData φ).hom ▷ (fpExtendScalars φ).obj X ≫
        (fpExtendScalars.μIsoData φ (𝟙_ _) X).hom ≫ (fpExtendScalars φ).map (λ_ X).hom := by
  have h :
      (λ_ ((fpExtendScalars φ).obj X)).inv =
        (fpExtendScalars φ).map (λ_ X).inv ≫
          (fpExtendScalars.μIsoData φ (𝟙_ _) X).inv ≫
          (fpExtendScalars.εIsoData φ).inv ▷ (fpExtendScalars φ).obj X := by
    letI : Algebra A B := φ.toAlgebra
    apply ObjectProperty.hom_ext
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change (ULift.up (1 : B)) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] x) =
      (fpExtendScalars.εLinearEquiv φ).symm
        ((fpExtendScalars.εLinearEquiv φ) (ULift.up (1 : B))) ⊗ₜ[B]
        ((1 : B) ⊗ₜ[A] x)
    rw [LinearEquiv.symm_apply_apply]
  rw [← cancel_mono (λ_ ((fpExtendScalars φ).obj X)).inv, Iso.hom_inv_id, h]
  simp only [Category.assoc, Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc,
    hom_inv_whiskerRight]


private theorem fpExtendScalars_right_unitality (φ : A →+* B)
    (X : (isFinitePresentation.{u, max u v} A).FullSubcategory) :
    (ρ_ ((fpExtendScalars φ).obj X)).hom =
      (fpExtendScalars φ).obj X ◁ (fpExtendScalars.εIsoData φ).hom ≫
        (fpExtendScalars.μIsoData φ X (𝟙_ _)).hom ≫ (fpExtendScalars φ).map (ρ_ X).hom := by
  have h :
      (ρ_ ((fpExtendScalars φ).obj X)).inv =
        (fpExtendScalars φ).map (ρ_ X).inv ≫
          (fpExtendScalars.μIsoData φ X (𝟙_ _)).inv ≫
          (fpExtendScalars φ).obj X ◁ (fpExtendScalars.εIsoData φ).inv := by
    letI : Algebra A B := φ.toAlgebra
    apply ObjectProperty.hom_ext
    apply ModuleCat.ExtendScalars.hom_ext
    intro x
    change ((1 : B) ⊗ₜ[A] x) ⊗ₜ[B] (ULift.up (1 : B)) =
      ((1 : B) ⊗ₜ[A] x) ⊗ₜ[B]
        (fpExtendScalars.εLinearEquiv φ).symm
          ((fpExtendScalars.εLinearEquiv φ) (ULift.up (1 : B)))
    rw [LinearEquiv.symm_apply_apply]
  rw [← cancel_mono (ρ_ ((fpExtendScalars φ).obj X)).inv, Iso.hom_inv_id, h]
  simp only [Category.assoc, Iso.map_hom_inv_id_assoc, Iso.hom_inv_id_assoc,
    whiskerLeft_hom_inv]


/-- The restricted extension-of-scalars functor is monoidal. -/
noncomputable instance fpExtendScalars.instMonoidal (φ : A →+* B) :
    (fpExtendScalars φ).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := fpExtendScalars.εIsoData φ
      μIso := fpExtendScalars.μIsoData φ
      μIso_hom_natural_left := by exact fpExtendScalars_μ_natural_left φ
      μIso_hom_natural_right := by exact fpExtendScalars_μ_natural_right φ
      associativity := by exact fpExtendScalars_associativity φ
      left_unitality := by exact fpExtendScalars_left_unitality φ
      right_unitality := by exact fpExtendScalars_right_unitality φ }

/-- The restricted extension-of-scalars functor is right exact. -/
instance fpExtendScalars.instPreservesFiniteColimits (φ : A →+* B) :
    PreservesFiniteColimits (fpExtendScalars φ) := by
  letI : HasCoequalizers (isFinitePresentation.{u, max u v} A).FullSubcategory :=
    Preadditive.hasCoequalizers_of_hasCokernels
  letI : HasFiniteBiproducts (isFinitePresentation.{u, max u v} A).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  letI : HasBinaryBiproducts (isFinitePresentation.{u, max u v} A).FullSubcategory :=
    hasBinaryBiproducts_of_finite_biproducts _
  letI : HasFiniteColimits (isFinitePresentation.{u, max u v} A).FullSubcategory :=
    hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
  letI : HasCoequalizers (isFinitePresentation.{v, max u v} B).FullSubcategory :=
    Preadditive.hasCoequalizers_of_hasCokernels
  letI : HasFiniteBiproducts (isFinitePresentation.{v, max u v} B).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteCoproducts
  letI : HasBinaryBiproducts (isFinitePresentation.{v, max u v} B).FullSubcategory :=
    hasBinaryBiproducts_of_finite_biproducts _
  letI : HasFiniteColimits (isFinitePresentation.{v, max u v} B).FullSubcategory :=
    hasFiniteColimits_of_hasCoequalizers_and_finite_coproducts
  letI : PreservesFiniteColimits
      (isFinitePresentation.{u, max u v} A).ι :=
    by
      letI preservesCokernel
          {X Y : (isFinitePresentation.{u, max u v} A).FullSubcategory} (f : X ⟶ Y) :
          PreservesColimit (parallelPair f 0) (isFinitePresentation.{u, max u v} A).ι :=
        (isFinitePresentation.{u, max u v} A).preservesCokernels_ι f
      exact Functor.preservesFiniteColimits_of_preservesCokernels
        (isFinitePresentation.{u, max u v} A).ι
  letI : PreservesFiniteColimits
      (isFinitePresentation.{v, max u v} B).ι :=
    by
      letI preservesCokernel
          {X Y : (isFinitePresentation.{v, max u v} B).FullSubcategory} (f : X ⟶ Y) :
          PreservesColimit (parallelPair f 0) (isFinitePresentation.{v, max u v} B).ι :=
        (isFinitePresentation.{v, max u v} B).preservesCokernels_ι f
      exact Functor.preservesFiniteColimits_of_preservesCokernels
        (isFinitePresentation.{v, max u v} B).ι
  letI : PreservesFiniteColimits (extendScalars φ) := by
    infer_instance
  letI : PreservesFiniteColimits
      ((isFinitePresentation.{u, max u v} A).ι ⋙ extendScalars φ) :=
    comp_preservesFiniteColimits _ _
  letI : PreservesFiniteColimits
      (fpExtendScalars φ ⋙ (isFinitePresentation.{v, max u v} B).ι) :=
    let e :
        (isFinitePresentation.{u, max u v} A).ι ⋙ extendScalars φ ≅
          fpExtendScalars φ ⋙ (isFinitePresentation.{v, max u v} B).ι :=
      Iso.refl _
    preservesFiniteColimits_of_natIso e
  exact preservesFiniteColimits_of_reflects_of_preserves
    (fpExtendScalars φ) (isFinitePresentation.{v, max u v} B).ι

/-- Restriction of extension of scalars agrees with unrestricted extension after inclusion. -/
noncomputable def fpExtendScalars_comp_ι (φ : A →+* B) :
    fpExtendScalars φ ⋙ (isFinitePresentation.{v, max u v} B).ι ≅
      (isFinitePresentation.{u, max u v} A).ι ⋙ extendScalars φ :=
  Iso.refl _

/-- Right-exact monoidal functors between finitely presented module categories. -/
structure RightExactMonoidalFpFunctor (A : Type u) [CommRing A] (B : Type v) [CommRing B] where
  /-- The underlying functor between finitely presented module categories. -/
  functor : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
    (isFinitePresentation.{v, max u v} B).FullSubcategory
  /-- The chosen monoidal structure on the underlying functor. -/
  monoidal : functor.Monoidal
  /-- Preservation of finite colimits by the underlying functor. -/
  rightExact : PreservesFiniteColimits functor

/-- A functor with a chosen monoidal structure and preservation of finite colimits defines a
right-exact monoidal functor between finitely presented module categories. -/
def RightExactMonoidalFpFunctor.ofFunctor
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    (monoidal : F.Monoidal) (rightExact : PreservesFiniteColimits F) :
    RightExactMonoidalFpFunctor A B where
  functor := F
  monoidal := monoidal
  rightExact := rightExact

/-- The functor constructed with a chosen monoidal structure stores that structure and
preserves finite colimits. -/
theorem RightExactMonoidalFpFunctor.ofFunctor_spec
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    (monoidal : F.Monoidal) (rightExact : PreservesFiniteColimits F) :
    (RightExactMonoidalFpFunctor.ofFunctor F monoidal rightExact).monoidal = monoidal ∧
      PreservesFiniteColimits
        (RightExactMonoidalFpFunctor.ofFunctor F monoidal rightExact).functor := by
  exact ⟨rfl, rightExact⟩

/-- Monoidal natural-isomorphism equivalence on right-exact monoidal functors. -/
def fpFunctorIsoSetoid (A : Type u) [CommRing A] (B : Type v) [CommRing B] :
    Setoid (RightExactMonoidalFpFunctor A B) where
  r F G :=
    -- Local instance justification (noncanonical choice): NatTrans.IsMonoidal must use F's stored monoidal structure through its class-parameterized compatibility interface.
    letI := F.monoidal
    -- Local instance justification (noncanonical choice): NatTrans.IsMonoidal must use G's stored monoidal structure rather than an independently inferred choice.
    letI := G.monoidal
    ∃ e : F.functor ≅ G.functor, NatTrans.IsMonoidal e.hom
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro F
      letI : F.functor.Monoidal := F.monoidal
      exact ⟨Iso.refl F.functor,
        (inferInstance : NatTrans.IsMonoidal (𝟙 F.functor))⟩
    · intro F G h
      letI : F.functor.Monoidal := F.monoidal
      letI : G.functor.Monoidal := G.monoidal
      obtain ⟨e, he⟩ := h
      letI : NatTrans.IsMonoidal e.hom := he
      exact ⟨e.symm, (inferInstance : NatTrans.IsMonoidal e.inv)⟩
    · intro F G H hFG hGH
      letI : F.functor.Monoidal := F.monoidal
      letI : G.functor.Monoidal := G.monoidal
      letI : H.functor.Monoidal := H.monoidal
      obtain ⟨e, he⟩ := hFG
      obtain ⟨f, hf⟩ := hGH
      letI : NatTrans.IsMonoidal e.hom := he
      letI : NatTrans.IsMonoidal f.hom := hf
      exact ⟨e ≪≫ f,
        (inferInstance : NatTrans.IsMonoidal (e.hom ≫ f.hom))⟩

/-- Isomorphism classes of right-exact monoidal functors between finitely presented module
categories. -/
abbrev rightExactMonoidalFpIsoClass (A : Type u) [CommRing A] (B : Type v) [CommRing B] :=
  Quotient (fpFunctorIsoSetoid A B)

/-- The isomorphism class represented by a right-exact monoidal functor. -/
def rightExactMonoidalFpIsoClass.mk
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
  [hM : F.Monoidal] [hR : PreservesFiniteColimits F] :
    rightExactMonoidalFpIsoClass A B :=
  Quotient.mk (fpFunctorIsoSetoid A B) (RightExactMonoidalFpFunctor.ofFunctor F hM hR)

/-- The class of restricted extension of scalars associated to a ring homomorphism. -/
noncomputable def ringHom_to_rightExactMonoidalFpIsoClass (φ : A →+* B) :
    rightExactMonoidalFpIsoClass A B :=
  rightExactMonoidalFpIsoClass.mk (fpExtendScalars φ)

/-- Every right-exact monoidal functor on finitely presented modules is monoidally naturally
isomorphic to restricted extension of scalars along a ring homomorphism. -/
theorem fpExtendScalars_iso_of
    (F : (isFinitePresentation.{u, max u v} A).FullSubcategory ⥤
      (isFinitePresentation.{v, max u v} B).FullSubcategory)
    [F.Monoidal] [PreservesFiniteColimits F] :
    ∃ φ : A →+* B, ∃ e : F ≅ fpExtendScalars φ, NatTrans.IsMonoidal e.hom := sorry

/-- Monoidally naturally isomorphic restricted extension-of-scalars functors arise from equal
ring homomorphisms. -/
theorem ringHom_eq_of_fpExtendScalars_iso {φ ψ : A →+* B}
    (h : ∃ e : fpExtendScalars φ ≅ fpExtendScalars ψ, NatTrans.IsMonoidal e.hom) :
    φ = ψ := by
  obtain ⟨e, he⟩ := h
  letI : NatTrans.IsMonoidal e.hom := he
  let U := 𝟙_ (isFinitePresentation.{u, max u v} A).FullSubcategory
  have heps (b : B) :
      (e.hom.app U).hom (fpExtendScalars.εLinearEquiv φ (ULift.up b)) =
        fpExtendScalars.εLinearEquiv ψ (ULift.up b) := by
    have hu := NatTrans.IsMonoidal.unit (τ := e.hom)
    exact congrArg (fun f => f.hom (ULift.up b)) hu
  ext a
  let r : U ⟶ U := ObjectProperty.homMk (ModuleCat.ofHom (a • LinearMap.id))
  have hs (χ : A →+* B) :
      ((fpExtendScalars χ).map r).hom (fpExtendScalars.εLinearEquiv χ (ULift.up (1 : B))) =
        fpExtendScalars.εLinearEquiv χ (ULift.up (χ a)) := by
    letI : Algebra A B := χ.toAlgebra
    change (1 : B) ⊗ₜ[A] (a • (ULift.up (1 : A) : ULift.{v, u} A)) =
      (χ a) ⊗ₜ[A] (ULift.up (1 : A))
    rw [TensorProduct.tmul_smul]
    change (χ a * 1) ⊗ₜ[A] (ULift.up (1 : A)) = _
    rw [mul_one]
  have hn := congrArg
    (fun f => f.hom (fpExtendScalars.εLinearEquiv φ (ULift.up (1 : B))))
    (e.hom.naturality r)
  change
    (e.hom.app U).hom
        (((fpExtendScalars φ).map r).hom (fpExtendScalars.εLinearEquiv φ (ULift.up (1 : B)))) =
      ((fpExtendScalars ψ).map r).hom
        ((e.hom.app U).hom (fpExtendScalars.εLinearEquiv φ (ULift.up (1 : B)))) at hn
  rw [hs φ, heps (φ a), heps 1, hs ψ] at hn
  exact congrArg ULift.down ((fpExtendScalars.εLinearEquiv ψ).injective hn)

/-- Ring homomorphisms classify right-exact monoidal functors between finitely presented module
categories up to monoidal natural isomorphism. -/
theorem ringHom_bijective_isoClass_rightExactMonoidalFp :
    Function.Bijective
      (ringHom_to_rightExactMonoidalFpIsoClass :
        (A →+* B) → rightExactMonoidalFpIsoClass A B) := by
  constructor
  · intro φ ψ h
    exact ringHom_eq_of_fpExtendScalars_iso (Quotient.exact h)
  · intro q
    obtain ⟨F, rfl⟩ := Quotient.exists_rep q
    letI : F.functor.Monoidal := F.monoidal
    letI : PreservesFiniteColimits F.functor := F.rightExact
    obtain ⟨φ, e, he⟩ := fpExtendScalars_iso_of F.functor
    refine ⟨φ, Quotient.sound ?_⟩
    letI : NatTrans.IsMonoidal e.hom := he
    exact ⟨e.symm, (inferInstance : NatTrans.IsMonoidal e.inv)⟩

end ModuleCat
