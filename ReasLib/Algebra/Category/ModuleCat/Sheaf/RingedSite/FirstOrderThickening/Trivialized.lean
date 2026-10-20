module

public import Mathlib.CategoryTheory.EpiMono
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.TrivSqZeroExt.Splitting
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.FirstOrderThickening
public import Mathlib.CategoryTheory.Category.Factorisation
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

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

/-- The projection from a trivial square-zero extension is locally surjective. -/
theorem fst_isLocallySurjective (O : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    Sheaf.IsLocallySurjective (fst O M) := sorry

/-- The kernel of the projection from a trivial square-zero extension is square zero. -/
theorem fst_isSquareZero (O : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    KernelIdeal.IsSquareZero (fst O M) := sorry

/-- The projection `O ⊕ M ⟶ O` is a first-order thickening. -/
instance instIsFirstOrderThickening_fst (O : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    IsFirstOrderThickening (fst O M) where
  isLocallySurjective := fst_isLocallySurjective O M
  isSquareZero := fst_isSquareZero O M

/-- The projection `O ⊕ M ⟶ O` is split by the algebra inclusion. -/
instance instIsSplitEpi_fst (O : Sheaf J CommRingCat.{max u v})
    (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    IsSplitEpi (fst O M) where
  exists_splitEpi := ⟨⟨inl O M, fst_comp_inl O M⟩⟩

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
  CommRingCat.ofHom (_root_.TrivSqZeroExt.map (f.val.app U).hom).toRingHom

/-- The induced square-zero extension map sends `(a, m)` to `(a, f(m))`. -/
theorem trivSqZeroExtMapApp_apply {O : Sheaf J CommRingCat.{max u v}}
    {M N : SheafOfModules.{max u v} (ringSheaf J O)} (f : M ⟶ N) (U : Cᵒᵖ)
    (x : (trivSqZeroExt O M).obj.obj U) :
    trivSqZeroExtMapApp f U x = trivSqZeroExtMapApply f U x := by
  apply _root_.TrivSqZeroExt.ext
  · exact _root_.TrivSqZeroExt.fst_map _ _
  · exact _root_.TrivSqZeroExt.snd_map _ _

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
    (h : SplitHom π₁ π₂ σ₁ σ₂) : h.hom ≫ π₂ = π₁ ∧ σ₁ ≫ h.hom = σ₂ :=
  ⟨h.comm, h.section_comm⟩

/-- Conjugating a kernel-module map by the splitting isomorphisms preserves projections. -/
theorem SplitHom.of_comm {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (f : KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂) :
    ((splittingIso π₁ σ₁ hσ₁ hI₁).hom ≫ trivSqZeroExtMap f ≫
      (splittingIso π₂ σ₂ hσ₂ hI₂).inv) ≫ π₂ = π₁ := sorry

/-- Conjugating a kernel-module map by the splitting isomorphisms preserves sections. -/
theorem SplitHom.of_section_comm {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (f : KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂) :
    σ₁ ≫ ((splittingIso π₁ σ₁ hσ₁ hI₁).hom ≫ trivSqZeroExtMap f ≫
      (splittingIso π₂ σ₂ hσ₂ hI₂).inv) = σ₂ := sorry

/-- The algebra map of trivialized thickenings associated to a module map of kernels. -/
def SplitHom.of {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (f : KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂) :
    SplitHom π₁ π₂ σ₁ σ₂ where
  hom := (splittingIso π₁ σ₁ hσ₁ hI₁).hom ≫ trivSqZeroExtMap f ≫
      (splittingIso π₂ σ₂ hσ₂ hI₂).inv
  comm := SplitHom.of_comm hσ₁ hσ₂ hI₁ hI₂ f
  section_comm := SplitHom.of_section_comm hσ₁ hσ₂ hI₁ hI₂ f

/-- A compatible square-zero algebra splitting supplies a section of its projection. -/
theorem splitEpiOfIso_id {O O' : Sheaf J CommRingCat.{max u v}}
    (π : O' ⟶ O) (I : SheafOfModules.{max u v} (ringSheaf J O))
    (e : O' ≅ trivSqZeroExt O I) (he : e.hom ≫ fst O I = π) :
    (inl O I ≫ e.inv) ≫ π = 𝟙 O := sorry

/-- An algebra identification respecting a specified projection supplies its section. -/
def splitEpiOfIso {O O' : Sheaf J CommRingCat.{max u v}}
    (π : O' ⟶ O) (I : SheafOfModules.{max u v} (ringSheaf J O))
    (e : O' ≅ trivSqZeroExt O I) (he : e.hom ≫ fst O I = π) :
    SplitEpi π where
  section_ := inl O I ≫ e.inv
  id := splitEpiOfIso_id π I e he

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

/-- The induced kernel map preserves zero on sections. -/
theorem homEquivToFunApply_zero {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) (U : Cᵒᵖ) :
    homEquivToFunApply hσ₁ hσ₂ hI₁ hI₂ h U 0 = 0 := sorry

/-- The induced kernel map preserves addition on sections. -/
theorem homEquivToFunApply_add {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) (U : Cᵒᵖ)
    (x y : (KernelIdeal.restrict π₁ σ₁).val.obj U) :
    homEquivToFunApply hσ₁ hσ₂ hI₁ hI₂ h U (x + y) =
      homEquivToFunApply hσ₁ hσ₂ hI₁ hI₂ h U x +
        homEquivToFunApply hσ₁ hσ₂ hI₁ hI₂ h U y := sorry

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
      map_zero' := homEquivToFunApply_zero hσ₁ hσ₂ hI₁ hI₂ h U
      map_add' := homEquivToFunApply_add hσ₁ hσ₂ hI₁ hI₂ h U }

/-- The induced additive kernel maps commute with restriction. -/
theorem homEquivToFunPresheaf_naturality {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) {U V : Cᵒᵖ} (rho : U ⟶ V) :
    (KernelIdeal.restrict π₁ σ₁).val.presheaf.map rho ≫
        homEquivToFunAdd hσ₁ hσ₂ hI₁ hI₂ h V =
      homEquivToFunAdd hσ₁ hσ₂ hI₁ hI₂ h U ≫
        (KernelIdeal.restrict π₂ σ₂).val.presheaf.map rho := sorry

/-- The underlying additive presheaf map of `homEquivToFun`. -/
def homEquivToFunPresheaf {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) :
    (KernelIdeal.restrict π₁ σ₁).val.presheaf ⟶
      (KernelIdeal.restrict π₂ σ₂).val.presheaf where
  app := homEquivToFunAdd hσ₁ hσ₂ hI₁ hI₂ h
  naturality := fun {_ _} rho ↦ homEquivToFunPresheaf_naturality hσ₁ hσ₂ hI₁ hI₂ h rho

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

/-- Reconstructing a section-preserving algebra map from its kernel map returns that map. -/
theorem homEquiv_left_inv {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (h : SplitHom π₁ π₂ σ₁ σ₂) :
    SplitHom.of hσ₁ hσ₂ hI₁ hI₂ (homEquivToFun hσ₁ hσ₂ hI₁ hI₂ h) = h := sorry

/-- Taking the kernel map of the reconstructed algebra map returns the module map. -/
theorem homEquiv_right_inv {O'₁ O'₂ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O'₁ ⟶ O} {π₂ : O'₂ ⟶ O} {σ₁ : O ⟶ O'₁} {σ₂ : O ⟶ O'₂}
    (hσ₁ : σ₁ ≫ π₁ = 𝟙 O) (hσ₂ : σ₂ ≫ π₂ = 𝟙 O)
    (hI₁ : KernelIdeal.IsSquareZero π₁) (hI₂ : KernelIdeal.IsSquareZero π₂)
    (f : KernelIdeal.restrict π₁ σ₁ ⟶ KernelIdeal.restrict π₂ σ₂) :
    homEquivToFun hσ₁ hσ₂ hI₁ hI₂ (SplitHom.of hσ₁ hσ₂ hI₁ hI₂ f) = f := sorry

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
  left_inv := homEquiv_left_inv hσ₁ hσ₂ hI₁ hI₂
  right_inv := homEquiv_right_inv hσ₁ hσ₂ hI₁ hI₂

/-- The identity map preserves a projection and its chosen section. -/
def SplitHom.id {O' O : Sheaf J CommRingCat.{max u v}}
    (π : O' ⟶ O) (σ : O ⟶ O') : SplitHom π π σ σ where
  hom := 𝟙 O'
  comm := Category.id_comp π
  section_comm := Category.comp_id σ

/-- Composition of maps preserving projections and chosen sections. -/
def SplitHom.comp {O₁ O₂ O₃ O : Sheaf J CommRingCat.{max u v}}
    {π₁ : O₁ ⟶ O} {π₂ : O₂ ⟶ O} {π₃ : O₃ ⟶ O}
    {σ₁ : O ⟶ O₁} {σ₂ : O ⟶ O₂} {σ₃ : O ⟶ O₃}
    (f : SplitHom π₁ π₂ σ₁ σ₂) (g : SplitHom π₂ π₃ σ₂ σ₃) :
    SplitHom π₁ π₃ σ₁ σ₃ where
  hom := f.hom ≫ g.hom
  comm := by rw [Category.assoc, g.comm, f.comm]
  section_comm := by rw [← Category.assoc, f.section_comm, g.section_comm]

/-- Trivialized first-order thickenings are factorizations of the identity whose projection
is locally surjective with square-zero kernel. Morphisms are covariant maps of ring sheaves
preserving both the section and the projection. Geometric morphisms reverse these ring maps. -/
abbrev Trivialized (O : Sheaf J CommRingCat.{max u v}) :=
  ObjectProperty.FullSubcategory
    ((fun d : Factorisation (𝟙 O) => IsFirstOrderThickening d.π) : ObjectProperty _)

variable {O : Sheaf J CommRingCat.{max u v}}

/-- A morphism of trivialized objects gives its explicit section-preserving ring map. -/
def Trivialized.toSplitHom {T S : Trivialized O} (f : T ⟶ S) :
    SplitHom T.obj.π S.obj.π T.obj.ι S.obj.ι where
  hom := f.hom.h
  comm := f.hom.h_π
  section_comm := f.hom.ι_h

/-- A section-preserving ring map defines a morphism of trivialized objects. -/
def Trivialized.ofSplitHom {T S : Trivialized O}
    (f : SplitHom T.obj.π S.obj.π T.obj.ι S.obj.ι) : T ⟶ S :=
  ObjectProperty.homMk { h := f.hom, ι_h := f.section_comm, h_π := f.comm }

/-- The trivialized thickening associated to a module is its trivial square-zero extension. -/
def Trivialized.ofModule (M : SheafOfModules.{max u v} (ringSheaf J O)) : Trivialized O :=
  ⟨{ mid := trivSqZeroExt O M, ι := inl O M, π := fst O M,
      ι_π := fst_comp_inl O M }, instIsFirstOrderThickening_fst O M⟩

/-- The kernel map of an identity is the identity. -/
theorem homEquivToFun_id (T : Trivialized O) :
    homEquivToFun T.obj.ι_π T.obj.ι_π T.property.isSquareZero T.property.isSquareZero
      (Trivialized.toSplitHom (𝟙 T)) = 𝟙 (KernelIdeal.restrict T.obj.π T.obj.ι) := sorry

/-- The kernel map of a composite is the composite of the kernel maps. -/
theorem homEquivToFun_comp {T S R : Trivialized O} (f : T ⟶ S) (g : S ⟶ R) :
    homEquivToFun T.obj.ι_π R.obj.ι_π T.property.isSquareZero R.property.isSquareZero
        (Trivialized.toSplitHom (f ≫ g)) =
      homEquivToFun T.obj.ι_π S.obj.ι_π T.property.isSquareZero S.property.isSquareZero
          (Trivialized.toSplitHom f) ≫
        homEquivToFun S.obj.ι_π R.obj.ι_π S.property.isSquareZero R.property.isSquareZero
          (Trivialized.toSplitHom g) := sorry

/-- The functor sending a trivialized thickening to its kernel module. -/
def idealFunctor (O : Sheaf J CommRingCat.{max u v}) :
    Trivialized O ⥤ SheafOfModules.{max u v} (ringSheaf J O) where
  obj T := KernelIdeal.restrict T.obj.π T.obj.ι
  map {T S} f := homEquivToFun T.obj.ι_π S.obj.ι_π
    T.property.isSquareZero S.property.isSquareZero (Trivialized.toSplitHom f)
  map_id := homEquivToFun_id
  map_comp := homEquivToFun_comp

/-- Square-zero extension maps preserve identity module maps. -/
theorem trivSqZeroExtMap_id (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    trivSqZeroExtMap (𝟙 M) = 𝟙 (trivSqZeroExt O M) := sorry

/-- Square-zero extension maps preserve composition of module maps. -/
theorem trivSqZeroExtMap_comp {M N P : SheafOfModules.{max u v} (ringSheaf J O)}
    (f : M ⟶ N) (g : N ⟶ P) :
    trivSqZeroExtMap (f ≫ g) = trivSqZeroExtMap f ≫ trivSqZeroExtMap g := sorry

/-- The functor sending a module to its canonically trivialized square-zero extension. -/
def ofModuleFunctor (O : Sheaf J CommRingCat.{max u v}) :
    SheafOfModules.{max u v} (ringSheaf J O) ⥤ Trivialized O where
  obj := Trivialized.ofModule
  map f := Trivialized.ofSplitHom
    { hom := trivSqZeroExtMap f
      comm := trivSqZeroExtMap_fst f
      section_comm := trivSqZeroExtMap_inl f }
  map_id M := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    exact trivSqZeroExtMap_id M
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    exact trivSqZeroExtMap_comp f g

/-- The module coordinate of a section of the kernel of a trivial square-zero extension. -/
def kernelToModuleApply (M : SheafOfModules.{max u v} (ringSheaf J O))
    (U : Cᵒᵖ) (x : (KernelIdeal.restrict (fst O M) (inl O M)).val.obj U) : M.val.obj U :=
  snd O M (KernelIdeal.ιApp (fst O M) U x)

/-- The kernel section represented by the square-zero summand of a module section. -/
def moduleToKernelApply (M : SheafOfModules.{max u v} (ringSheaf J O))
    (U : Cᵒᵖ) (m : M.val.obj U) :
    (KernelIdeal.restrict (fst O M) (inl O M)).val.obj U :=
  (KernelIdeal.sectionsIso (fst O M) U).inv ⟨inr O M m, rfl⟩

/-- The module coordinate of a kernel section preserves zero. -/
theorem kernelToModule_zero (M : SheafOfModules.{max u v} (ringSheaf J O)) (U : Cᵒᵖ) :
    kernelToModuleApply M U 0 = 0 := sorry

/-- The module coordinate of a kernel section preserves addition. -/
theorem kernelToModule_add (M : SheafOfModules.{max u v} (ringSheaf J O)) (U : Cᵒᵖ)
    (x y : (KernelIdeal.restrict (fst O M) (inl O M)).val.obj U) :
    kernelToModuleApply M U (x + y) = kernelToModuleApply M U x + kernelToModuleApply M U y := sorry

/-- The additive map taking a kernel section to its module coordinate. -/
def kernelToModuleAdd (M : SheafOfModules.{max u v} (ringSheaf J O)) (U : Cᵒᵖ) :
    (KernelIdeal.restrict (fst O M) (inl O M)).val.presheaf.obj U ⟶ M.val.presheaf.obj U :=
  AddCommGrpCat.ofHom
    { toFun := kernelToModuleApply M U
      map_zero' := kernelToModule_zero M U
      map_add' := kernelToModule_add M U }

/-- Taking the module coordinate of kernel sections commutes with restrictions. -/
theorem kernelToModule_naturality (M : SheafOfModules.{max u v} (ringSheaf J O))
    {U V : Cᵒᵖ} (rho : U ⟶ V) :
    (KernelIdeal.restrict (fst O M) (inl O M)).val.presheaf.map rho ≫ kernelToModuleAdd M V =
      kernelToModuleAdd M U ≫ M.val.presheaf.map rho := sorry

/-- The additive presheaf map taking kernel sections to their module coordinates. -/
def kernelToModulePresheaf (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    (KernelIdeal.restrict (fst O M) (inl O M)).val.presheaf ⟶ M.val.presheaf where
  app := kernelToModuleAdd M
  naturality := fun {_ _} rho ↦ kernelToModule_naturality M rho

/-- The module coordinate of a kernel section is linear over the base ring. -/
theorem kernelToModule_smul (M : SheafOfModules.{max u v} (ringSheaf J O))
    (U : Cᵒᵖ) (r : (ringSheaf J O).obj.obj U)
    (x : (KernelIdeal.restrict (fst O M) (inl O M)).val.obj U) :
    (kernelToModulePresheaf M).app U (r • x) = r • (kernelToModulePresheaf M).app U x := sorry

/-- The module coordinate identifies the kernel of a trivial square-zero extension with its module. -/
def kernelToModule (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    KernelIdeal.restrict (fst O M) (inl O M) ⟶ M :=
  ⟨PresheafOfModules.homMk (kernelToModulePresheaf M) (kernelToModule_smul M)⟩

/-- Inclusion of module sections in the kernel preserves zero. -/
theorem moduleToKernel_zero (M : SheafOfModules.{max u v} (ringSheaf J O)) (U : Cᵒᵖ) :
    moduleToKernelApply M U 0 = 0 := sorry

/-- Inclusion of module sections in the kernel preserves addition. -/
theorem moduleToKernel_add (M : SheafOfModules.{max u v} (ringSheaf J O)) (U : Cᵒᵖ)
    (x y : M.val.obj U) :
    moduleToKernelApply M U (x + y) = moduleToKernelApply M U x + moduleToKernelApply M U y := sorry

/-- The additive inclusion of module sections into the kernel of the projection. -/
def moduleToKernelAdd (M : SheafOfModules.{max u v} (ringSheaf J O)) (U : Cᵒᵖ) :
    M.val.presheaf.obj U ⟶ (KernelIdeal.restrict (fst O M) (inl O M)).val.presheaf.obj U :=
  AddCommGrpCat.ofHom
    { toFun := moduleToKernelApply M U
      map_zero' := moduleToKernel_zero M U
      map_add' := moduleToKernel_add M U }

/-- Inclusion of module sections in the kernel commutes with restriction. -/
theorem moduleToKernel_naturality (M : SheafOfModules.{max u v} (ringSheaf J O))
    {U V : Cᵒᵖ} (rho : U ⟶ V) :
    M.val.presheaf.map rho ≫ moduleToKernelAdd M V =
      moduleToKernelAdd M U ≫ (KernelIdeal.restrict (fst O M) (inl O M)).val.presheaf.map rho := sorry

/-- The additive presheaf inclusion of module sections into the kernel of the projection. -/
def moduleToKernelPresheaf (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    M.val.presheaf ⟶ (KernelIdeal.restrict (fst O M) (inl O M)).val.presheaf where
  app := moduleToKernelAdd M
  naturality := fun {_ _} rho ↦ moduleToKernel_naturality M rho

/-- Inclusion of module sections in the kernel is linear over the base ring. -/
theorem moduleToKernel_smul (M : SheafOfModules.{max u v} (ringSheaf J O))
    (U : Cᵒᵖ) (r : (ringSheaf J O).obj.obj U) (x : M.val.obj U) :
    (moduleToKernelPresheaf M).app U (r • x) = r • (moduleToKernelPresheaf M).app U x := sorry

/-- The module inclusion induces a map to the kernel of its trivial square-zero extension. -/
def moduleToKernel (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    M ⟶ KernelIdeal.restrict (fst O M) (inl O M) :=
  ⟨PresheafOfModules.homMk (moduleToKernelPresheaf M) (moduleToKernel_smul M)⟩

/-- Extracting the module coordinate and including it back is the identity on the kernel. -/
theorem kernelModuleIso_hom_inv_id (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    kernelToModule M ≫ moduleToKernel M = 𝟙 _ := sorry

/-- Including a module section and extracting its coordinate is the identity. -/
theorem kernelModuleIso_inv_hom_id (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    moduleToKernel M ≫ kernelToModule M = 𝟙 M := sorry

/-- The kernel of a trivial square-zero extension is canonically its module. -/
def kernelModuleIso (M : SheafOfModules.{max u v} (ringSheaf J O)) :
    KernelIdeal.restrict (fst O M) (inl O M) ≅ M where
  hom := kernelToModule M
  inv := moduleToKernel M
  hom_inv_id := kernelModuleIso_hom_inv_id M
  inv_hom_id := kernelModuleIso_inv_hom_id M

/-- The splitting isomorphism identifies a trivialized thickening with the model of its kernel. -/
def unitApp (T : Trivialized O) :
    T ≅ (ofModuleFunctor O).obj ((idealFunctor O).obj T) where
  hom := ObjectProperty.homMk
    { h := (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).hom
      ι_h := by
        apply (cancel_mono (splittingIso T.obj.π T.obj.ι T.obj.ι_π
          T.property.isSquareZero).inv).1
        change (T.obj.ι ≫ (splittingIso T.obj.π T.obj.ι T.obj.ι_π
          T.property.isSquareZero).hom) ≫
            (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).inv =
          inl O (KernelIdeal.restrict T.obj.π T.obj.ι) ≫
            (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).inv
        rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]
        exact (splittingInv_comp_inl T.obj.π T.obj.ι T.property.isSquareZero).symm
      h_π := splittingHom_comp_fst T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero }
  inv := ObjectProperty.homMk
    { h := (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).inv
      ι_h := splittingInv_comp_inl T.obj.π T.obj.ι T.property.isSquareZero
      h_π := by
        apply (cancel_epi (splittingIso T.obj.π T.obj.ι T.obj.ι_π
          T.property.isSquareZero).hom).1
        change (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).hom ≫
            ((splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).inv ≫ T.obj.π) =
          (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).hom ≫
            fst O (KernelIdeal.restrict T.obj.π T.obj.ι)
        rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
        exact (splittingHom_comp_fst T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).symm }
  hom_inv_id := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    exact (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).hom_inv_id
  inv_hom_id := by
    apply ObjectProperty.hom_ext
    apply Factorisation.Hom.ext
    exact (splittingIso T.obj.π T.obj.ι T.obj.ι_π T.property.isSquareZero).inv_hom_id

/-- Splitting by the chosen section is natural in section-preserving ring maps. -/
theorem unitApp_naturality {T S : Trivialized O} (f : T ⟶ S) :
    f ≫ (unitApp S).hom =
      (unitApp T).hom ≫ ((idealFunctor O) ⋙ (ofModuleFunctor O)).map f := sorry

/-- The natural identification of a trivialized thickening with the model of its kernel. -/
def unitIso (O : Sheaf J CommRingCat.{max u v}) :
    𝟭 (Trivialized O) ≅ idealFunctor O ⋙ ofModuleFunctor O :=
  NatIso.ofComponents unitApp (fun f ↦ unitApp_naturality f)

/-- Identifying the kernel of a square-zero extension with its module is natural. -/
theorem kernelModuleIso_naturality {M N : SheafOfModules.{max u v} (ringSheaf J O)}
    (f : M ⟶ N) :
    (ofModuleFunctor O ⋙ idealFunctor O).map f ≫ (kernelModuleIso N).hom =
      (kernelModuleIso M).hom ≫ f := sorry

/-- The natural identification of the kernel of a square-zero model with its module. -/
def counitIso (O : Sheaf J CommRingCat.{max u v}) :
    ofModuleFunctor O ⋙ idealFunctor O ≅ 𝟭 (SheafOfModules.{max u v} (ringSheaf J O)) :=
  NatIso.ofComponents kernelModuleIso (fun f ↦ kernelModuleIso_naturality f)

/-- Trivialized first-order thickenings in the covariant ring-sheaf presentation are equivalent
 to modules over the base ring sheaf. -/
def modulesEquiv (O : Sheaf J CommRingCat.{max u v}) :
    Trivialized O ≌ SheafOfModules.{max u v} (ringSheaf J O) :=
  CategoryTheory.Equivalence.mk (idealFunctor O) (ofModuleFunctor O) (unitIso O) (counitIso O)

end SheafOfModules.RingedSite.FirstOrderThickening
