/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Torsor.Defs
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Extension.Infinitesimal

/-!
# Compatible maps of mixed-scalar extensions

For a same-site square-zero thickening π : 𝒪' ⟶ 𝒪, compatible maps of extensions
carry an additive translation by morphisms between the quotient and kernel.
-/

@[expose] public section

open CategoryTheory
open SheafOfModules.RingedSite

noncomputable section

universe u v

namespace SheafOfModules.RingedSite
namespace FirstOrderThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {𝒪' 𝒪 : Sheaf J CommRingCat.{max u v}} {π : 𝒪' ⟶ 𝒪}
variable (F G : Extension π) (φ : F.quot ⟶ G.quot) (ψ : F.kernel ⟶ G.kernel)

/-- An 𝒪'-module map ℱ' ⟶ 𝒢' compatible with 𝒪-module maps φ : ℱ ⟶ 𝒢 and
ψ : 𝒦 ⟶ ℒ. -/
structure CompatibleMap where
  /-- The underlying 𝒪'-module morphism ℱ' ⟶ 𝒢'. -/
  hom : F.middle ⟶ G.middle
  /-- Compatibility with the inclusions of the kernels 𝒦 ⟶ ℒ. -/
  comm_ι : F.ι ≫ hom = (restrictionAlong π).map ψ ≫ G.ι
  /-- Compatibility with the projections onto the quotients ℱ ⟶ 𝒢. -/
  comm_p : hom ≫ G.p = F.p ≫ (restrictionAlong π).map φ

namespace CompatibleMap

/-- Assemble a compatible 𝒪'-module map from a middle morphism and its commuting squares. -/
def of (hom : F.middle ⟶ G.middle)
    (hι : CommSq F.ι ((restrictionAlong π).map ψ) hom G.ι)
    (hp : CommSq hom F.p G.p ((restrictionAlong π).map φ)) :
    CompatibleMap F G φ ψ where
  hom := hom
  comm_ι := hι.w
  comm_p := hp.w

/-- A compatible map induces both kernel and quotient squares. -/
theorem spec (f : CompatibleMap F G φ ψ) :
    CommSq F.ι ((restrictionAlong π).map ψ) f.hom G.ι ∧
      CommSq f.hom F.p G.p ((restrictionAlong π).map φ) :=
  ⟨⟨f.comm_ι⟩, ⟨f.comm_p⟩⟩

/-- The kernel square for the Hom_𝒪(ℱ, ℒ)-translate of a compatible map. -/
theorem vadd_comm_ι (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    F.ι ≫ (f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι)) =
      (restrictionAlong π).map ψ ≫ G.ι := by
  simp [Preadditive.comp_add, ← Category.assoc, f.comm_ι, F.zero]

/-- The quotient square for the Hom_𝒪(ℱ, ℒ)-translate of a compatible map. -/
theorem vadd_comm_p (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    (f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι)) ≫ G.p =
      F.p ≫ (restrictionAlong π).map φ := by
  simp [Preadditive.add_comp, Category.assoc, f.comm_p, G.zero]

/-- Translate a compatible map by an 𝒪-module morphism α : ℱ ⟶ ℒ. -/
def vadd (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    CompatibleMap F G φ ψ where
  hom := f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι)
  comm_ι := vadd_comm_ι F G φ ψ α f
  comm_p := vadd_comm_p F G φ ψ α f

/-- The underlying middle map of a Hom_𝒪(ℱ, ℒ)-translate. -/
theorem vadd_hom (α : F.quot ⟶ G.kernel) (f : CompatibleMap F G φ ψ) :
    (vadd F G φ ψ α f).hom = f.hom + (F.p ≫ (restrictionAlong π).map α ≫ G.ι) := rfl

/-- The kernel square of the associated short-complex morphism. -/
theorem toHom_comm₁₂ (f : CompatibleMap F G φ ψ) :
    (restrictionAlong π).map ψ ≫ G.ι = F.ι ≫ f.hom := f.comm_ι.symm

/-- The quotient square of the associated short-complex morphism. -/
theorem toHom_comm₂₃ (f : CompatibleMap F G φ ψ) :
    f.hom ≫ G.p = F.p ≫ (restrictionAlong π).map φ := f.comm_p

/-- The morphism of mixed-scalar short complexes with restricted endpoints φ and ψ. -/
def toHom (f : CompatibleMap F G φ ψ) : shortComplex F ⟶ shortComplex G :=
  ShortComplex.homMk ((restrictionAlong π).map ψ) f.hom ((restrictionAlong π).map φ)
    (toHom_comm₁₂ F G φ ψ f) (toHom_comm₂₃ F G φ ψ f)

/-- Any two compatible maps differ by a unique 𝒪-module morphism ℱ ⟶ ℒ. -/
theorem existsUnique_vsub [Sheaf.IsLocallySurjective π]
    (f g : CompatibleMap F G φ ψ) :
    ∃! α : F.quot ⟶ G.kernel, vadd F G φ ψ α g = f := by
  letI : Presheaf.IsLocallySurjective J (ringSheafMap π).hom :=
    ⟨fun s ↦ Presheaf.imageSieve_mem J π.hom s⟩
  letI := F.shortExact.mono_f
  letI := G.shortExact.mono_f
  letI := F.shortExact.epi_g
  let d : F.middle ⟶ G.middle := f.hom - g.hom
  have hd_p : d ≫ G.p = 0 := by
    dsimp [d]
    rw [Preadditive.sub_comp, f.comm_p, g.comm_p, sub_self]
  have hιd : F.ι ≫ d = 0 := by
    dsimp [d]
    rw [Preadditive.comp_sub, f.comm_ι, g.comm_ι, sub_self]
  let β : F.middle ⟶ (restrictionAlong π).obj G.kernel :=
    G.shortExact.exact.lift d hd_p
  have hβι : F.ι ≫ β = 0 := by
    apply (cancel_mono G.ι).1
    rw [Category.assoc, G.shortExact.exact.lift_f, hιd]
    simp
  let γ : (restrictionAlong π).obj F.quot ⟶ (restrictionAlong π).obj G.kernel :=
    F.shortExact.exact.desc β hβι
  have hγ : F.p ≫ γ = β := F.shortExact.exact.g_desc β hβι
  let α : F.quot ⟶ G.kernel :=
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (ringSheafMap π).hom G.kernel.isSheaf).symm γ.val⟩
  have hα : (restrictionAlong π).map α = γ := by
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      (ringSheafMap π).hom G.kernel.isSheaf).apply_symm_apply γ.val
  have hhom : (vadd F G φ ψ α g).hom = f.hom := by
    rw [vadd_hom, hα, ← Category.assoc, hγ, G.shortExact.exact.lift_f]
    dsimp [d]
    abel
  have hom_ext : ∀ {x y : CompatibleMap F G φ ψ}, x.hom = y.hom → x = y := by
    intro x y h
    cases x with
    | mk xh xi xp =>
      cases y with
      | mk yh yi yp =>
        cases h
        rfl
  have heq : vadd F G φ ψ α g = f := hom_ext hhom
  refine ⟨α, heq, ?_⟩
  intro α' hα'
  have hhom' : (vadd F G φ ψ α' g).hom = f.hom :=
    congrArg CompatibleMap.hom hα'
  have hterms : F.p ≫ (restrictionAlong π).map α' ≫ G.ι =
      F.p ≫ (restrictionAlong π).map α ≫ G.ι := by
    apply add_left_cancel
    rw [vadd_hom] at hhom' hhom
    exact hhom'.trans hhom.symm
  have hmaps : (restrictionAlong π).map α' = (restrictionAlong π).map α := by
    apply (cancel_epi F.p).1
    apply (cancel_mono G.ι).1
    exact hterms
  apply SheafOfModules.hom_ext
  exact (PresheafOfModules.restrictScalars (ringSheafMap π).hom).map_injective
    (congrArg SheafOfModules.Hom.val hmaps)

end CompatibleMap

variable [J.HasSheafCompose (forget₂ RingCat.{max u v} AddCommGrpCat.{max u v})]
variable [HasWeakSheafify J CommRingCat.{max u v}]
variable [J.WEqualsLocallyBijective CommRingCat.{max u v}]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]

/-- A compatible map intertwines the infinitesimal maps of its two extensions. -/
theorem infMap_commSq (hπ : KernelIdeal.IsSquareZero π) [Sheaf.IsLocallySurjective π]
    (f : CompatibleMap F G φ ψ) :
    CommSq (infMap hπ F) (moduleTensorMap (𝟙 (idealModule hπ)) φ) ψ (infMap hπ G) :=
  sorry

/-- Compatible maps of mixed-scalar extensions, if they exist, form a principal
homogeneous space under morphisms from the quotient to the kernel. -/
theorem compatibleMap_isEmpty_or_addTorsor (hπ : KernelIdeal.IsSquareZero π)
    [Sheaf.IsLocallySurjective π] :
    IsEmpty (CompatibleMap F G φ ψ) ∨
      Nonempty (AddTorsor (F.quot ⟶ G.kernel) (CompatibleMap F G φ ψ)) :=
  by
    classical
    rcases isEmpty_or_nonempty (CompatibleMap F G φ ψ) with h | h
    · exact Or.inl h
    · right
      have hom_ext : ∀ {x y : CompatibleMap F G φ ψ}, x.hom = y.hom → x = y := by
        intro x y hxy
        cases x with
        | mk xh xi xp =>
          cases y with
          | mk yh yi yp =>
            cases hxy
            rfl
      letI : Presheaf.IsLocallySurjective J (ringSheafMap π).hom :=
        ⟨fun s ↦ Presheaf.imageSieve_mem J π.hom s⟩
      letI := G.shortExact.mono_f
      letI := F.shortExact.epi_g
      have hd_p (f g : CompatibleMap F G φ ψ) : (f.hom - g.hom) ≫ G.p = 0 := by
        rw [Preadditive.sub_comp, f.comm_p, g.comm_p, sub_self]
      let β (f g : CompatibleMap F G φ ψ) :
          F.middle ⟶ (restrictionAlong π).obj G.kernel :=
        G.shortExact.exact.lift (f.hom - g.hom) (hd_p f g)
      have hβι (f g : CompatibleMap F G φ ψ) : F.ι ≫ β f g = 0 := by
        apply (cancel_mono G.ι).1
        rw [Category.assoc, G.shortExact.exact.lift_f,
          Preadditive.comp_sub, f.comm_ι, g.comm_ι, sub_self]
        simp
      let γ (f g : CompatibleMap F G φ ψ) :
          (restrictionAlong π).obj F.quot ⟶ (restrictionAlong π).obj G.kernel :=
        F.shortExact.exact.desc (β f g) (hβι f g)
      let δ (f g : CompatibleMap F G φ ψ) : F.quot ⟶ G.kernel :=
        ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective
          (ringSheafMap π).hom G.kernel.isSheaf).symm (γ f g).val⟩
      have hδ (f g : CompatibleMap F G φ ψ) :
          CompatibleMap.vadd F G φ ψ (δ f g) g = f := by
        apply hom_ext
        have hmap : (restrictionAlong π).map (δ f g) = γ f g := by
          apply SheafOfModules.hom_ext
          exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
            (ringSheafMap π).hom G.kernel.isSheaf).apply_symm_apply (γ f g).val
        rw [CompatibleMap.vadd_hom, hmap, ← Category.assoc,
          F.shortExact.exact.g_desc, G.shortExact.exact.lift_f]
        abel
      exact ⟨{
        vadd := CompatibleMap.vadd F G φ ψ
        zero_vadd := fun f ↦ by
          change CompatibleMap.vadd F G φ ψ 0 f = f
          apply hom_ext
          simp [CompatibleMap.vadd_hom]
        add_vadd := fun α β f ↦ by
          change CompatibleMap.vadd F G φ ψ (α + β) f =
            CompatibleMap.vadd F G φ ψ α (CompatibleMap.vadd F G φ ψ β f)
          apply hom_ext
          simp only [CompatibleMap.vadd_hom, Functor.map_add,
            Preadditive.comp_add, Preadditive.add_comp]
          abel
        vsub := δ
        nonempty := h
        vsub_vadd' := hδ
        vadd_vsub' := fun α f ↦ by
          change δ (CompatibleMap.vadd F G φ ψ α f) f = α
          exact (CompatibleMap.existsUnique_vsub F G φ ψ
            (CompatibleMap.vadd F G φ ψ α f) f).unique (hδ _ _) rfl }⟩

end FirstOrderThickening
end SheafOfModules.RingedSite
