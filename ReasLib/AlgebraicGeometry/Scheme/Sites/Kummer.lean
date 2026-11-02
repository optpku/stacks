/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Kummer
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.CommRing
import all ReasLib.Algebra.Category.Ring.Sheaf.Units
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Field.ULift
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Tactic.NormNum
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.EpiMono
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Flat
import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.FinitePresentation
import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Kummer

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.AssociatedModule

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme

/-- Local surjectivity of the power map persists when the topology is enlarged. -/
private theorem kummerShortExact_of_le {C : Type u} [Category.{v} C]
    {J K : GrothendieckTopology C} (hJK : J ≤ K)
    (F : Cᵒᵖ ⥤ CommRingCat.{max u v})
    (hF : Presheaf.IsSheaf J F) (hF' : Presheaf.IsSheaf K F) (n : ℕ)
    (h : (Sheaf.kummerAddShortComplex ⟨F, hF⟩ n).ShortExact) :
    (Sheaf.kummerAddShortComplex ⟨F, hF'⟩ n).ShortExact := by
  have h_epi : Epi (Sheaf.unitsNsmul ⟨F, hF⟩ n) := h.epi_g
  have h_loc : Sheaf.IsLocallySurjective (Sheaf.unitsNsmul ⟨F, hF⟩ n) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat
      (Sheaf.unitsNsmul ⟨F, hF⟩ n)).2 h_epi
  have h_loc' : Sheaf.IsLocallySurjective (Sheaf.unitsNsmul ⟨F, hF'⟩ n) := by
    constructor
    intro U s
    exact hJK U (Presheaf.imageSieve_mem J (Sheaf.unitsNsmul ⟨F, hF⟩ n).hom s)
  exact
    { exact := ShortComplex.kernelSequence_exact (Sheaf.unitsNsmul ⟨F, hF'⟩ n)
      mono_f := by
        dsimp [Sheaf.kummerAddShortComplex]
        infer_instance
      epi_g := by
        change Epi (Sheaf.unitsNsmul ⟨F, hF'⟩ n)
        infer_instance }

private theorem kummerEtaleTopology_le_smooth (S : Scheme.{u}) :
    StandardTopology.etale.overTopology S ≤ StandardTopology.smooth.overTopology S := by
  intro U R hR
  exact Scheme.grothendieckTopology_monotone
    (fun X Y f hf => by
      letI : Etale f := hf
      infer_instance) U.left hR

/-- The Kummer short complex is short exact on the big syntomic site of a scheme
when the exponent is a positive natural number. -/
theorem kummerBigSyntomicShortExact
    (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .syntomic S) n).ShortExact := sorry

/-- The Kummer short complex is short exact on the big fppf site of a scheme
when the exponent is a positive natural number. -/
theorem kummerBigFppfShortExact
    (S : Scheme.{u}) (n : ℕ) (h_pos : 0 < n) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .fppf S) n).ShortExact := by
  have hτ : StandardTopology.syntomic.overTopology S ≤
      StandardTopology.fppf.overTopology S := by
    intro U R hR
    exact Scheme.grothendieckTopology_monotone
      (fun X Y f hf => by
        letI : Syntomic f := hf
        exact ⟨inferInstance, inferInstance⟩) U.left hR
  exact kummerShortExact_of_le hτ _ _ _ n (kummerBigSyntomicShortExact S n h_pos)

private theorem kummerZariskiCover_eq_top (S : Scheme.{u}) (U : Over S)
    [Subsingleton U.left] [Nonempty U.left] (R : Sieve U)
    (hR : R ∈ (Scheme.zariskiTopology.over S) U) : R = ⊤ := by
  obtain ⟨𝒰, hle⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hR
  have hcover := (Scheme.ofArrows_mem_precoverage_iff _).mp 𝒰.mem₀
  obtain ⟨i, x, _hx⟩ := hcover.1 (Classical.choice (inferInstance : Nonempty U.left))
  letI : IsOpenImmersion (𝒰.f i) := hcover.2 i
  haveI : Epi (𝒰.f i).base := (TopCat.epi_iff_surjective _).2
    (fun y => ⟨x, Subsingleton.elim _ _⟩)
  haveI : IsIso (𝒰.f i) := IsOpenImmersion.isIso (𝒰.f i)
  let f : Over.mk (𝒰.f i ≫ U.hom) ⟶ U := Over.homMk (𝒰.f i)
  haveI : IsIso ((Over.forget S).map f) := inferInstanceAs (IsIso (𝒰.f i))
  haveI : IsIso f := isIso_of_reflects_iso f (Over.forget S)
  have hf : R f := (Sieve.overEquiv_iff R (𝒰.f i)).mp (hle _ _ ⟨i⟩)
  apply Sieve.id_mem_iff_eq_top.mp
  simpa using R.downward_closed hf (inv f)


private theorem kummerZariski_app_surjective (S : Scheme.{u}) (U : Over S)
    [Subsingleton U.left] [Nonempty U.left]
    {F G : Sheaf (Scheme.zariskiTopology.over S) AddCommGrpCat.{u + 1}}
    (φ : F ⟶ G) [Epi φ] : Function.Surjective (φ.hom.app (op U)) := by
  have hloc := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat φ).2 inferInstance
  intro s
  have hmem := Presheaf.imageSieve_mem (Scheme.zariskiTopology.over S) φ.hom s
  have hid : Presheaf.imageSieve φ.hom s (𝟙 U) := by
    rw [kummerZariskiCover_eq_top S U _ hmem]
    trivial
  simpa only [Presheaf.imageSieve_apply, op_id, G.obj.map_id,
    ConcreteCategory.id_apply] using hid


/-- The Kummer short complex can fail to be short exact on the big Zariski site
even when the exponent is positive and invertible on the base scheme. -/
theorem kummerBigZariskiNotShortExact :
    ∃ (S : Scheme.{u}) (n : ℕ),
      0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧
        ¬ (CategoryTheory.Sheaf.kummerAddShortComplex
          (bigCommStructureSheaf .zariski S) n).ShortExact := by
  let A := ULift.{u} ℚ
  let S : Scheme.{u} := Spec (CommRingCat.of A)
  let U : Over S := Over.mk (𝟙 S)
  let O := bigCommStructureSheaf .zariski S
  haveI : Subsingleton U.left := inferInstanceAs (Subsingleton (PrimeSpectrum A))
  haveI : Nonempty U.left := inferInstanceAs (Nonempty (PrimeSpectrum A))
  have hA : (2 : A) ≠ 0 := by
    intro h
    have h' := congrArg ULift.down h
    norm_num [A] at h'
  refine ⟨S, 2, by decide, ?_, ?_⟩
  · simpa only [map_ofNat, Nat.cast_ofNat] using (isUnit_iff_ne_zero.mpr hA).map
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  · intro h
    haveI : Epi (Sheaf.unitsNsmul O 2) := h.epi_g
    let s : (Sheaf.unitsAddSheaf O).obj.obj (op U) :=
      Additive.ofMul (-1 : (ULift.{u + 1} Γ(S, ⊤))ˣ)
    obtain ⟨t, ht⟩ := kummerZariski_app_surjective S U (Sheaf.unitsNsmul O 2) s
    have hsmul : (2 : ℕ) • t = s := by
      simpa [Sheaf.unitsNsmul, two_nsmul, Sheaf.Hom.add_app] using ht
    have hsmul' : (2 : ℕ) • (t : Additive ((ULift.{u + 1} Γ(S, ⊤))ˣ)) =
        Additive.ofMul (-1 : (ULift.{u + 1} Γ(S, ⊤))ˣ) := by
      exact hsmul
    let t' : (ULift.{u + 1} Γ(S, ⊤))ˣ := Additive.toMul t
    have hunit : t' ^ (2 : ℕ) = -1 := by
      exact congrArg (@Additive.toMul ((ULift.{u + 1} Γ(S, ⊤))ˣ)) hsmul'
    have hsq : t'.val ^ (2 : ℕ) = -1 := by
      simpa using congrArg Units.val hunit
    let e : ULift.{u + 1} Γ(S, ⊤) →+* ℚ :=
      ULift.ringEquiv.toRingHom.comp
        ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp ULift.ringEquiv.toRingHom)
    have hsq' : e t'.val ^ (2 : ℕ) = (-1 : ℚ) := by
      simpa only [map_pow, map_neg, map_one] using congrArg e hsq
    have hn := sq_nonneg (e t'.val)
    rw [hsq'] at hn
    norm_num at hn

/-- The Kummer short complex is short exact on the big smooth site of a scheme
when the exponent is invertible on the base scheme. -/
theorem kummerBigSmoothShortExact
    (S : Scheme.{u}) (n : ℕ) (h_n : IsUnit (n : Γ(S, ⊤))) :
    (CategoryTheory.Sheaf.kummerAddShortComplex
      (bigCommStructureSheaf .smooth S) n).ShortExact := by
  exact kummerShortExact_of_le (kummerEtaleTopology_le_smooth S) _ _ _ n
    (kummerBigEtaleShortExact S n h_n)

/-- The Kummer short complex is not short exact for every positive exponent on
the big smooth site of schemes. -/
theorem kummerBigSmoothNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .smooth S) n).ShortExact := sorry

/-- The Kummer short complex is not short exact for every positive exponent on
the big étale site of schemes. -/
theorem kummerBigEtaleNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .etale S) n).ShortExact := by
  intro h
  apply kummerBigSmoothNotUniversallyShortExact.{u}
  intro S n h_pos
  exact kummerShortExact_of_le (kummerEtaleTopology_le_smooth S) _ _ _ n (h S n h_pos)

/-- The Kummer short complex is not short exact for every positive exponent on
the big Zariski site of schemes. -/
theorem kummerBigZariskiNotUniversallyShortExact :
    ¬ ∀ (S : Scheme.{u}) (n : ℕ), 0 < n →
      (CategoryTheory.Sheaf.kummerAddShortComplex
        (bigCommStructureSheaf .zariski S) n).ShortExact := by
  intro h
  obtain ⟨S, n, h_pos, _, h_not⟩ := kummerBigZariskiNotShortExact.{u}
  exact h_not (h S n h_pos)

end AlgebraicGeometry.Scheme

end
