/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap60.Definition_60_11_1_ModuleProperties
public import stacks_project.Chap60.Remark_60_6_8_Connection
public import stacks_project.Chap60.Remark_60_13_1
public import stacks_project.Chap60.Remark_60_13_2
public import ReasLib.LinearAlgebra.ExteriorPower.LeftTensor
public import ReasLib.RingTheory.Kaehler.DeRham
public import ReasLib.RingTheory.Kaehler.DeRham.Wedge
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.RingTheory.Kaehler.Basic

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrystallineObject
open scoped AlgebraicGeometry RelativeDerivation TensorProduct

@[expose] public section

universe u

namespace CrisModuleSheaf

variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}

/-- Global sections of the structure sheaf of a small crystalline thickening. -/
noncomputable def sectionRing (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Γ(T.obj.1.thickening, ⊤)

/-- Global sections of a crystalline module sheaf on a thickening. -/
noncomputable def sectionModule (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Γ(F.obj T, ⊤)

/-- Global sections of `Ω[T/S]`. -/
noncomputable def oneForms (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Γ(Ω[T.obj.1.thickeningToBase.toShHom], ⊤)

/-- The structure morphism of a thickening induces the algebra `Γ(S) → Γ(T)`. -/
noncomputable instance sectionRingAlgebra
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Algebra Γ(S, ⊤) (sectionRing T) :=
  (T.obj.1.thickeningToBase.app ⊤).hom.toAlgebra

/-- One-forms are a module over the thickening section ring. -/
noncomputable instance oneFormsModule
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Module (sectionRing T) (oneForms T) :=
  inferInstanceAs (Module Γ(T.obj.1.thickening, ⊤)
    Γ(Ω[T.obj.1.thickeningToBase.toShHom], ⊤))

/-- One-forms are a module over `Γ(S)`. -/
noncomputable instance oneFormsModuleBase
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Module Γ(S, ⊤) (oneForms T) :=
  Module.compHom (oneForms T) (algebraMap Γ(S, ⊤) (sectionRing T))

/-- The scalar actions of `Γ(S)` and `Γ(T)` on one-forms are compatible. -/
instance oneFormsIsScalarTower
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    IsScalarTower Γ(S, ⊤) (sectionRing T) (oneForms T) := sorry

/-- Exterior powers of `Ω[T/S,δ]` are modules over `Γ(S)` via the scalar tower. -/
noncomputable instance formModuleBase
    (T : smallCrystallineSite S I γ h_compatible X x₀) (p : ℕ) :
    Module Γ(S, ⊤) (exteriorPower.form (sectionRing T) (oneForms T) p) :=
  exteriorPower.form.moduleOfScalarTower p

/-- Exterior powers of algebraic `Ω[Γ(T)/Γ(S)]` are modules over `Γ(S)` via the scalar tower. -/
noncomputable instance algebraicFormModuleBase
    (T : smallCrystallineSite S I γ h_compatible X x₀) (p : ℕ) :
    Module Γ(S, ⊤)
      (exteriorPower.form (sectionRing T) Ω[sectionRing T ⁄ Γ(S, ⊤)] p) :=
  exteriorPower.form.moduleOfScalarTower p

/-- Global sections of a crystalline module are a module over `Γ(T)`. -/
noncomputable instance sectionModuleModule
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Module (sectionRing T) (sectionModule F T) :=
  inferInstanceAs (Module Γ(T.obj.1.thickening, ⊤) Γ(F.obj T, ⊤))

/-- The universal derivation `d[T/S]` on global sections. -/
noncomputable def universalDerivation
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Derivation Γ(S, ⊤) (sectionRing T) (oneForms T) where
  toFun := fun f ↦ (d[T.obj.1.thickeningToBase.toShHom]).d f
  map_add' := sorry
  map_smul' := sorry
  map_one_eq_zero' := sorry
  leibniz' := sorry

/-- Applying `universalDerivation` recovers `d[T/S]` on global sections. -/
theorem universalDerivation_apply
    (T : smallCrystallineSite S I γ h_compatible X x₀) (f : sectionRing T) :
    universalDerivation T f = (d[T.obj.1.thickeningToBase.toShHom]).d f := sorry

/-- Pull a global section of a module sheaf along a scheme morphism. -/
noncomputable def pullbackSection {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    Γ((Scheme.Modules.pullback g).obj M, ⊤) :=
  (Scheme.Modules.Hom.app
      ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ⊤).hom s

/-- The comparison isomorphism `c₀` along `p₀`. -/
noncomputable def comparisonP0 (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (Scheme.Modules.pullback
        (FirstOrderThickening.p₀ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T) ⟶
      F.obj (FirstOrderThickening.object I γ h_compatible x₀ T) :=
  F.comparison (FirstOrderThickening.p₀ I γ h_compatible x₀ T)

/-- The comparison isomorphism `c₁` along `p₁`. -/
noncomputable def comparisonP1 (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (Scheme.Modules.pullback
        (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T) ⟶
      F.obj (FirstOrderThickening.object I γ h_compatible x₀ T) :=
  F.comparison (FirstOrderThickening.p₁ I γ h_compatible x₀ T)

/-- The crystal transition `c = c₁⁻¹ ≫ c₀` on the first-order thickening. -/
noncomputable def crystalTransition (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    (Scheme.Modules.pullback
        (FirstOrderThickening.p₀ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T) ⟶
    (Scheme.Modules.pullback
        (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T) :=
  comparisonP0 F T ≫
    inv (F.comparison (FirstOrderThickening.p₁ I γ h_compatible x₀ T))

/-- The section `p₁^* s` of `p₁^* ℱ_T`. -/
noncomputable def pullbackP1Section (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    Γ((Scheme.Modules.pullback
        (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T), ⊤) :=
  pullbackSection (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening
    (F.obj T) s

/-- The section `c(p₀^* s)` of `p₁^* ℱ_T`. -/
noncomputable def transitionP0Section (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    Γ((Scheme.Modules.pullback
        (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T), ⊤) :=
  (Scheme.Modules.Hom.app (crystalTransition F T) ⊤).hom
    (pullbackSection (FirstOrderThickening.p₀ I γ h_compatible x₀ T).hom.thickening
      (F.obj T) s)

/-- The difference `p₁^* s - c(p₀^* s)` before the kernel identification. -/
noncomputable def connectionDifference (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    Γ((Scheme.Modules.pullback
        (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T), ⊤) :=
  pullbackP1Section F T s - transitionP0Section F T s

/-- Global sections of the first-order square-zero thickening `T'`. -/
noncomputable def firstOrderSectionRing
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Γ((FirstOrderThickening.object I γ h_compatible x₀ T).obj.1.thickening, ⊤)

/-- The square-zero inclusion of a one-form as a global section of `𝒪_{T'}`. -/
noncomputable def inrOneForm
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (ω : oneForms T) :
    firstOrderSectionRing T :=
  (TrivSqZeroExt.inr ω : TrivSqZeroExt (sectionRing T) (oneForms T))

/-- The first-order thickening ring acts on `p₁^* ℱ_T`. -/
noncomputable instance pullbackP1Module
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Module (firstOrderSectionRing T)
      Γ((Scheme.Modules.pullback
          (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
        (F.obj T), ⊤) :=
  inferInstanceAs
    (Module Γ((FirstOrderThickening.object I γ h_compatible x₀ T).obj.1.thickening, ⊤)
      Γ((Scheme.Modules.pullback
          (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
        (F.obj T), ⊤))

/-- Square-zero action of a one-form on a pulled-back section: `ω · p₁^* s`. -/
noncomputable def formAction
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) (ω : oneForms T) :
    Γ((Scheme.Modules.pullback
        (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T), ⊤) :=
  inrOneForm T ω • pullbackP1Section F T s

/-- Global sections of `p₁^* ℱ_T`. -/
noncomputable def pullbackP1Carrier (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  Γ((Scheme.Modules.pullback
      (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
    (F.obj T), ⊤)

/-- Pullback of sections along the crystalline inclusion `i : T ⟶ T'`. -/
noncomputable def inclusionStar (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    pullbackP1Carrier F T →+
      Γ((Scheme.Modules.pullback
          (FirstOrderThickening.inclusion I γ h_compatible x₀ T).hom.thickening).obj
        ((Scheme.Modules.pullback
            (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
          (F.obj T)), ⊤) where
  toFun := pullbackSection
    (FirstOrderThickening.inclusion I γ h_compatible x₀ T).hom.thickening
    ((Scheme.Modules.pullback
        (FirstOrderThickening.p₁ I γ h_compatible x₀ T).hom.thickening).obj
      (F.obj T))
  map_zero' := sorry
  map_add' := sorry

/-- The kernel of `i^*` on global sections of `p₁^* ℱ_T`. -/
noncomputable def inclusionStarKernel (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :=
  AddMonoidHom.ker (inclusionStar F T)

/-- The square-zero action of a one-form lands in `ker(i^*)`. -/
noncomputable def formActionKer (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) (ω : oneForms T) :
    inclusionStarKernel F T :=
  ⟨formAction F T s ω, sorry⟩

/-- Embed `ℱ_T ⊗ Ω[T/S,δ]` into `ker(i^*)` by the square-zero action of one-forms. -/
noncomputable def tensorEmbed (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    sectionModule F T ⊗[sectionRing T] oneForms T →+ inclusionStarKernel F T :=
  TensorProduct.liftAddHom
    { toFun := fun s ↦
        { toFun := fun ω ↦ formActionKer F T s ω
          map_zero' := sorry
          map_add' := sorry }
      map_zero' := sorry
      map_add' := sorry }
    (fun _ _ _ ↦ sorry)

/-- The square-zero embedding is bijective onto the kernel of `i^*`. -/
theorem tensorEmbed_bijective
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Function.Bijective (tensorEmbed F T) := sorry

/-- Kernel identification `ℱ_T ⊗ Ω[T/S,δ] ≃ ker(i^*)`. -/
noncomputable def tensorEmbedEquiv
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    sectionModule F T ⊗[sectionRing T] oneForms T ≃+ inclusionStarKernel F T :=
  AddEquiv.ofBijective (tensorEmbed F T) (tensorEmbed_bijective F T)

/-- The difference `p₁^* s - c(p₀^* s)` lies in `ker(i^*)`. -/
theorem connectionDifference_mem_ker
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    connectionDifference F T s ∈ inclusionStarKernel F T := sorry

/-- The explicit global-section value of the canonical crystal connection. -/
noncomputable def canonicalConnectionValue
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    sectionModule F T ⊗[sectionRing T] oneForms T :=
  (tensorEmbedEquiv F T).symm ⟨connectionDifference F T s, connectionDifference_mem_ker F T s⟩

/-- The embedding of the canonical connection value recovers `p₁^*s - c(p₀^*s)`. -/
theorem canonicalConnectionValue_spec
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    (tensorEmbed F T (canonicalConnectionValue F T s)).val =
      connectionDifference F T s := sorry

/-- The additive map of the canonical crystal connection. -/
noncomputable def canonicalConnectionHom
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    sectionModule F T →+ sectionModule F T ⊗[sectionRing T] oneForms T where
  toFun := canonicalConnectionValue F T
  map_zero' := sorry
  map_add' := sorry

/-- The canonical integrable connection on global sections of a crystal. -/
noncomputable def canonicalConnection
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Connection (universalDerivation T) (sectionModule F T) :=
  Connection.of (canonicalConnectionHom F T) (fun _ _ ↦ sorry)

/-- Evaluating the canonical connection recovers the unique tensor with the
`p₁^*s - c(p₀^*s)` embedding formula. -/
theorem canonicalConnection_apply
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    Connection.apply (canonicalConnection F T) s =
      canonicalConnectionValue F T s := sorry

/-- Leibniz rule for the canonical crystal connection. -/
theorem canonicalConnection_leibniz
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (f : sectionRing T) (s : sectionModule F T) :
    Connection.apply (canonicalConnection F T) (f • s) =
      f • Connection.apply (canonicalConnection F T) s +
        s ⊗ₜ[sectionRing T] universalDerivation T f := sorry


/-- Unfolding for `sectionRing`. -/
theorem sectionRing_eq (T : smallCrystallineSite S I γ h_compatible X x₀) :
    sectionRing T = Γ(T.obj.1.thickening, ⊤) := sorry

/-- Unfolding for `sectionModule`. -/
theorem sectionModule_eq (F : CrisModuleSheaf S I γ h_compatible X x₀)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    sectionModule F T = Γ(F.obj T, ⊤) := sorry

/-- Unfolding for `oneForms`. -/
theorem oneForms_eq (T : smallCrystallineSite S I γ h_compatible X x₀) :
    oneForms T = Γ(Ω[T.obj.1.thickeningToBase.toShHom], ⊤) := sorry

/-- Unfolding for `pullbackSection`. -/
theorem pullbackSection_apply {Y Z : Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) (s : Γ(M, ⊤)) :
    pullbackSection g M s =
      (Scheme.Modules.Hom.app
          ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M) ⊤).hom s := sorry

/-- Unfolding for `comparisonP0`. -/
theorem comparisonP0_eq (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    comparisonP0 F T =
      F.comparison (FirstOrderThickening.p₀ I γ h_compatible x₀ T) := sorry

/-- Unfolding for `comparisonP1`. -/
theorem comparisonP1_eq (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    comparisonP1 F T =
      F.comparison (FirstOrderThickening.p₁ I γ h_compatible x₀ T) := sorry

/-- Unfolding for `crystalTransition`. -/
theorem crystalTransition_eq (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    crystalTransition F T =
      comparisonP0 F T ≫
        inv (F.comparison (FirstOrderThickening.p₁ I γ h_compatible x₀ T)) := sorry

/-- Unfolding for `connectionDifference`. -/
theorem connectionDifference_eq (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    connectionDifference F T s =
      pullbackP1Section F T s - transitionP0Section F T s := sorry

/-- Pure tensors are sent to the corresponding pulled-back sections. -/
theorem tensorEmbed_tmul (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (x : sectionModule F T) (ω : oneForms T) :
    (tensorEmbed F T (x ⊗ₜ[sectionRing T] ω)).val = formAction F T x ω := sorry

/-- The comparison from algebraic Kähler differentials of `Γ(T)/Γ(S)` to `Ω[T/S]`. -/
noncomputable def kaehlerToOneForms
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Ω[sectionRing T ⁄ Γ(S, ⊤)] →ₗ[sectionRing T] oneForms T :=
  Derivation.liftKaehlerDifferential (universalDerivation T)

/-- The comparison is bijective on global sections of a thickening. -/
theorem kaehlerToOneForms_bijective
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Function.Bijective (kaehlerToOneForms T) := sorry

/-- Identification of algebraic Kähler differentials with global sections of `Ω[T/S]`. -/
noncomputable def kaehlerToOneFormsEquiv
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Ω[sectionRing T ⁄ Γ(S, ⊤)] ≃ₗ[sectionRing T] oneForms T :=
  LinearEquiv.ofBijective (kaehlerToOneForms T) (kaehlerToOneForms_bijective T)

/-- Evaluation of presented algebraic forms in the standard exterior-power module. -/
noncomputable def toExteriorEquiv (p : ℕ)
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    KaehlerDifferential.DeRham.Form Γ(S, ⊤) (sectionRing T) p ≃ₗ[sectionRing T]
      exteriorPower.form (sectionRing T) Ω[sectionRing T ⁄ Γ(S, ⊤)] p :=
  LinearEquiv.ofBijective
    (KaehlerDifferential.DeRham.toExterior Γ(S, ⊤) (sectionRing T) p).hom
    (KaehlerDifferential.DeRham.toExterior_bijective Γ(S, ⊤) (sectionRing T) p)

/-- The algebraic de Rham differential on exterior powers of `Ω[Γ(T)/Γ(S)]`. -/
noncomputable def algebraicDeRhamFamily
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    DifferentialOperator.DeRham.Family Γ(S, ⊤) (sectionRing T)
      Ω[sectionRing T ⁄ Γ(S, ⊤)] :=
  fun p ↦
    { toFun := fun ω ↦
        (toExteriorEquiv (p + 1) T)
          (Submodule.Quotient.restrictScalarsEquiv Γ(S, ⊤)
            (KaehlerDifferential.DeRham.relations Γ(S, ⊤) (sectionRing T) (p + 1))
            ((KaehlerDifferential.DeRham.rawD Γ(S, ⊤) (sectionRing T) p).hom
              ((Submodule.Quotient.restrictScalarsEquiv Γ(S, ⊤)
                  (KaehlerDifferential.DeRham.relations Γ(S, ⊤) (sectionRing T) p)).symm
                ((toExteriorEquiv p T).symm ω))))
      map_add' := sorry
      map_smul' := sorry }

/-- The canonical de Rham family of `Ω[T/S,δ]` on global sections. -/
noncomputable def deRhamFamily
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    DifferentialOperator.DeRham.Family Γ(S, ⊤) (sectionRing T) (oneForms T) :=
  fun p ↦
    { toFun := fun ω ↦
        exteriorPower.form.mapRestrictScalars Γ(S, ⊤)
          (kaehlerToOneFormsEquiv T).toLinearMap (p + 1)
          (algebraicDeRhamFamily T p
            (exteriorPower.form.mapRestrictScalars Γ(S, ⊤)
              (kaehlerToOneFormsEquiv T).symm.toLinearMap p ω))
      map_add' := sorry
      map_smul' := sorry }

/-- Left wedge by a one-form on the global exterior calculus of `T`. -/
noncomputable def leftWedge
    (T : smallCrystallineSite S I γ h_compatible X x₀) (p : ℕ) :
    oneForms T →ₗ[sectionRing T]
      exteriorPower.form (sectionRing T) (oneForms T) p →ₗ[sectionRing T]
        exteriorPower.form (sectionRing T) (oneForms T) (p + 1) :=
  match p with
  | 0 => (LinearMap.lsmul (sectionRing T) (oneForms T)).flip
  | 1 => LinearMap.mk₂ (sectionRing T)
      (fun η ξ ↦ exteriorPower.leftWedgeOne (R := sectionRing T) η ξ)
      (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)
  | n + 2 => LinearMap.mk₂ (sectionRing T)
      (fun η ω ↦ exteriorPower.leftWedge (R := sectionRing T) η (n + 2) ω)
      (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- Transport an exterior form along the algebraic Kähler comparison. -/
noncomputable def formToAlgebraic (T : smallCrystallineSite S I γ h_compatible X x₀)
    (p : ℕ) :
    exteriorPower.form (sectionRing T) (oneForms T) p →ₗ[sectionRing T]
      KaehlerDifferential.DeRham.Form Γ(S, ⊤) (sectionRing T) p where
  toFun ω :=
    (toExteriorEquiv p T).symm
      (exteriorPower.form.mapRestrictScalars Γ(S, ⊤)
        (kaehlerToOneFormsEquiv T).symm.toLinearMap p ω)
  map_add' := sorry
  map_smul' := sorry

/-- Transport an algebraic form back to `Ω[T/S]` exterior powers. -/
noncomputable def algebraicToForm (T : smallCrystallineSite S I γ h_compatible X x₀)
    (p : ℕ) :
    KaehlerDifferential.DeRham.Form Γ(S, ⊤) (sectionRing T) p →ₗ[sectionRing T]
      exteriorPower.form (sectionRing T) (oneForms T) p where
  toFun ω :=
    exteriorPower.form.mapRestrictScalars Γ(S, ⊤)
      (kaehlerToOneFormsEquiv T).toLinearMap p (toExteriorEquiv p T ω)
  map_add' := sorry
  map_smul' := sorry

/-- Left wedge by a two-form via the algebraic exterior product on `Ω[Γ(T)/Γ(S)]`. -/
noncomputable def leftWedgeTwo
    (T : smallCrystallineSite S I γ h_compatible X x₀) (p : ℕ) :
    exteriorPower.form (sectionRing T) (oneForms T) 2 →ₗ[sectionRing T]
      exteriorPower.form (sectionRing T) (oneForms T) p →ₗ[sectionRing T]
        exteriorPower.form (sectionRing T) (oneForms T) (p + 2) :=
  LinearMap.mk₂ (sectionRing T)
    (fun τ ω ↦
      cast (congrArg (exteriorPower.form (sectionRing T) (oneForms T)) (Nat.add_comm 2 p))
        (algebraicToForm T (2 + p)
          (KaehlerDifferential.DeRham.formWedgeBilinear Γ(S, ⊤) (sectionRing T) 2 p
            (formToAlgebraic T 2 τ) (formToAlgebraic T p ω))))
    (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry) (fun _ _ _ ↦ sorry)

/-- The named divided-power de Rham exterior calculus of `Ω[T/S,δ]` on `T`. -/
noncomputable def exteriorCalculus
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    ExteriorCalculus (universalDerivation T) (deRhamFamily T) :=
  ExteriorCalculus.of
    (leftWedge T)
    (leftWedgeTwo T)
    (fun _ _ _ ↦ sorry)
    (fun _ _ _ ↦ sorry)
    (fun _ _ _ _ ↦ sorry)
    sorry

/-- Unfolding for `canonicalConnectionHom`. -/
theorem canonicalConnectionHom_apply
    (F : CrisModuleSheaf S I γ h_compatible X x₀)
    [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀)
    (s : sectionModule F T) :
    canonicalConnectionHom F T s = canonicalConnectionValue F T s := sorry

end CrisModuleSheaf

end
