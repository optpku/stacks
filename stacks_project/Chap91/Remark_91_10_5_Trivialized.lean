/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.EpiMono
public import stacks_project.Chap91.«91_10_5_1_Splitting»
public import stacks_project.Chap91.Remark_91_10_10_Thickening

/-!
# Trivialized first-order thickenings of a ringed topos

After identifying underlying topoi, a first-order thickening `π : O' ⟶ O` is trivial when it
admits a section. The canonical objects are trivial square-zero extensions `O ⊕ I`, and
section-compatible algebra maps over `O` correspond to maps of `O`-modules.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.TrivSqZeroExt

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]

/-- A first-order thickening `π : O' ⟶ O` is trivial when the projection is a split epimorphism. -/
class IsTrivial {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O)
    [IsFirstOrderThickening π] : Prop where
  [isSplitEpi : IsSplitEpi π]

attribute [instance] IsTrivial.isSplitEpi

/-- A first-order thickening is trivial iff its projection is a split epimorphism. -/
theorem isTrivial_iff {O' O : Sheaf J CommRingCat.{max u v}} (π : O' ⟶ O)
    [IsFirstOrderThickening π] : IsTrivial π ↔ IsSplitEpi π := sorry

/-- The projection `O ⊕ M ⟶ O` is a first-order thickening. -/
instance instIsFirstOrderThickening_fst (O : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    IsFirstOrderThickening (fst O M) where
  isLocallySurjective := sorry
  isSquareZero := sorry

/-- The projection `O ⊕ M ⟶ O` is split by the algebra inclusion. -/
instance instIsSplitEpi_fst (O : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    IsSplitEpi (fst O M) where
  exists_splitEpi := ⟨⟨inl O M, fst_comp_inl O M⟩⟩

/-- The projection `O ⊕ M ⟶ O` is a trivial first-order thickening. -/
instance instIsTrivial_fst (O : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    IsTrivial (fst O M) where

/-- The algebra map `O ⊕ M ⟶ O ⊕ N` associated to an `O`-module map, on sections. -/
def trivSqZeroExtMapApply {O : Sheaf J CommRingCat.{max u v}}
    {M N : SheafOfModules.{max u v} (ringSheaf J O)} (f : M ⟶ N)
    (U : Cᵒᵖ) (x : (trivSqZeroExt O M).obj.obj U) :
    (trivSqZeroExt O N).obj.obj U :=
  (x.1, f.val.app U x.2)

/-- The component of `trivSqZeroExtMap` over an object of the site. -/
def trivSqZeroExtMapApp {O : Sheaf J CommRingCat.{max u v}}
    {M N : SheafOfModules.{max u v} (ringSheaf J O)} (f : M ⟶ N) (U : Cᵒᵖ) :
    (trivSqZeroExt O M).obj.obj U ⟶ (trivSqZeroExt O N).obj.obj U :=
  CommRingCat.ofHom
    { toFun := trivSqZeroExtMapApply f U
      map_zero' := sorry
      map_one' := sorry
      map_add' := sorry
      map_mul' := sorry }

/-- The components of `trivSqZeroExtMap` commute with restriction. -/
theorem trivSqZeroExtMapApp_naturality {O : Sheaf J CommRingCat.{max u v}}
    {M N : SheafOfModules.{max u v} (ringSheaf J O)} (f : M ⟶ N) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    (trivSqZeroExt O M).obj.map rho ≫ trivSqZeroExtMapApp f V =
      trivSqZeroExtMapApp f U ≫ (trivSqZeroExt O N).obj.map rho := sorry

/-- An `O`-module map `M ⟶ N` induces an algebra map `O ⊕ M ⟶ O ⊕ N`. -/
def trivSqZeroExtMap {O : Sheaf J CommRingCat.{max u v}}
    {M N : SheafOfModules.{max u v} (ringSheaf J O)} (f : M ⟶ N) :
    trivSqZeroExt O M ⟶ trivSqZeroExt O N :=
  ObjectProperty.homMk
    { app := trivSqZeroExtMapApp f
      naturality := fun {_ _} rho ↦ trivSqZeroExtMapApp_naturality f rho }

/-- `trivSqZeroExtMap` commutes with the algebra projections. -/
theorem trivSqZeroExtMap_fst {O : Sheaf J CommRingCat.{max u v}}
    {M N : SheafOfModules.{max u v} (ringSheaf J O)} (f : M ⟶ N) :
    trivSqZeroExtMap f ≫ fst O N = fst O M := sorry

/-- `trivSqZeroExtMap` commutes with the algebra inclusions. -/
theorem trivSqZeroExtMap_inl {O : Sheaf J CommRingCat.{max u v}}
    {M N : SheafOfModules.{max u v} (ringSheaf J O)} (f : M ⟶ N) :
    inl O M ≫ trivSqZeroExtMap f = inl O N := sorry

/-- A morphism of trivialized first-order thickenings of `O` is an algebra map over `O`
that intertwines the chosen sections. -/
structure SplitHom {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    (π₁ : O'₁ ⟶ O) (π₂ : O'₂ ⟶ O) (σ₁ : O ⟶ O'₁) (σ₂ : O ⟶ O'₂) where
  /-- The morphism of thickened ring sheaves `O'₁ ⟶ O'₂`. -/
  hom : O'₁ ⟶ O'₂
  /-- The morphism lies over `O`. -/
  comm : hom ≫ π₂ = π₁
  /-- The morphism intertwines the chosen trivializations. -/
  section_comm : σ₁ ≫ hom = σ₂

/-- A `SplitHom` is an algebra map over `O` compatible with the chosen sections. -/
theorem SplitHom.spec {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (h : SplitHom π₁ π₂ σ₁ σ₂) : h.hom ≫ π₂ = π₁ ∧ σ₁ ≫ h.hom = σ₂ := sorry

/-- The algebra map of trivialized thickenings associated to an `O`-module map of kernels. -/
def SplitHom.of {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (f : KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂) :
    SplitHom π₁ π₂ σ₁ σ₂ where
  hom := (splittingIso π₁ σ₁ hσ₁ hI₁).hom ≫ trivSqZeroExtMap f ≫
    (splittingIso π₂ σ₂ hσ₂ hI₂).inv
  comm := sorry
  section_comm := sorry

/-- An algebra identification with a trivial square-zero extension supplies a section of the
projection. -/
def splitEpiOfIso {O O' : Sheaf J CommRingCat.{max u v}}
    (I : SheafOfModules.{max u v} (ringSheaf J O)) (e : O' ≅ trivSqZeroExt O I) :
    SplitEpi (e.hom ≫ fst O I) where
  section_ := inl O I ≫ e.inv
  id := sorry

/-- Transport of a morphism of trivialized thickenings to a map of trivial square-zero
extensions of the kernel modules. -/
def splitHomToTrivSqZeroExt {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) :
    trivSqZeroExt O (KernelIdeal.restrict π₁ σ₁) ⟶
      trivSqZeroExt O (KernelIdeal.restrict π₂ σ₂) :=
  (splittingIso π₁ σ₁ hσ₁ hI₁).inv ≫ h.hom ≫ (splittingIso π₂ σ₂ hσ₂ hI₂).hom

/-- The kernel-module map associated to a morphism of trivialized thickenings, on sections. -/
def homEquivToFunApply {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) (U : Cᵒᵖ)
    (m : (KernelIdeal.restrict π₁ σ₁).val.obj U) :
    (KernelIdeal.restrict π₂ σ₂).val.obj U :=
  snd O (KernelIdeal.restrict π₂ σ₂)
    ((splitHomToTrivSqZeroExt hσ₁ hσ₂ hI₁ hI₂ h).hom.app U
      (inr O (KernelIdeal.restrict π₁ σ₁) m))

/-- The underlying additive component of `homEquivToFun` over an object of the site. -/
def homEquivToFunAdd {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) (U : Cᵒᵖ) :
    (KernelIdeal.restrict π₁ σ₁).val.presheaf.obj U ⟶
      (KernelIdeal.restrict π₂ σ₂).val.presheaf.obj U :=
  AddCommGrpCat.ofHom
    { toFun := homEquivToFunApply hσ₁ hσ₂ hI₁ hI₂ h U
      map_zero' := sorry
      map_add' := sorry }

/-- The underlying additive presheaf map of `homEquivToFun`. -/
def homEquivToFunPresheaf {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) :
    (KernelIdeal.restrict π₁ σ₁).val.presheaf ⟶
      (KernelIdeal.restrict π₂ σ₂).val.presheaf where
  app := homEquivToFunAdd hσ₁ hσ₂ hI₁ hI₂ h
  naturality := sorry

/-- Linearity of the additive kernel map of a morphism of trivialized thickenings. -/
theorem homEquivToFun_smul {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) (U : Cᵒᵖ)
    (r : (ringSheaf J O).obj.obj U)
    (m : (KernelIdeal.restrict π₁ σ₁).val.obj U) :
    (homEquivToFunPresheaf hσ₁ hσ₂ hI₁ hI₂ h).app U (r • m) =
      r • (homEquivToFunPresheaf hσ₁ hσ₂ hI₁ hI₂ h).app U m := sorry

/-- The kernel-module map associated to a morphism of trivialized thickenings. -/
def homEquivToFun {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) :
    KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂ :=
  ⟨PresheafOfModules.homMk (homEquivToFunPresheaf hσ₁ hσ₂ hI₁ hI₂ h)
      (homEquivToFun_smul hσ₁ hσ₂ hI₁ hI₂ h)⟩

/-- Morphisms of trivialized first-order thickenings of `O` correspond to morphisms of the
kernel `O`-modules. -/
def homEquiv {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂) :
    SplitHom π₁ π₂ σ₁ σ₂ ≃
      (KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂) where
  toFun := homEquivToFun hσ₁ hσ₂ hI₁ hI₂
  invFun := SplitHom.of hσ₁ hσ₂ hI₁ hI₂
  left_inv := sorry
  right_inv := sorry

end SheafOfModules.RingedSite.FirstOrderThickening
