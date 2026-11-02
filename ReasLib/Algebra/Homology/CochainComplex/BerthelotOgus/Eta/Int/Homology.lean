/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Integer-indexed eta homology comparison

The divided-coordinate model identifies the class of a cycle in `K` with the class of the same
cycle in `eta f K`.  In the localization presentation of `eta`, this is the usual degree-`i`
scaling map; keeping divided coordinates makes the owner uniform for every `i : ℤ`.
@stack 0F7P
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int

variable {A : Type u} [CommRing A]

/-- Consecutive integer degrees are related by the cochain-complex shape. -/
theorem rel_succ (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := rfl

/-- A cycle of `K` is an element of the corresponding divided-coordinate eta term. -/
theorem cycle_mem (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (x : K.cycles i) : (K.iCycles i).hom x ∈ term f K i := by
  have hz : K.d i (i + 1) ((K.iCycles i) x) = 0 :=
    congrArg (fun g : K.cycles i ⟶ K.X (i + 1) ↦ g x) (K.iCycles_d i (i + 1))
  change K.d i (i + 1) ((K.iCycles i) x) ∈
    LinearMap.range (LinearMap.lsmul A (K.X (i + 1)) f)
  rw [hz]
  exact Submodule.zero_mem _

/-- The cycle inclusion into an integer eta term. -/
@[stacks 0F7P "cycle inclusion into the integer eta term"]
def cycleLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    K.cycles i →ₗ[A] term f K i :=
  (K.iCycles i).hom.codRestrict _ (cycle_mem f K i)

/-- The cycle inclusion has zero composite with the divided eta differential. -/
theorem cycle_comp_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) (i : ℤ) :
    ModuleCat.ofHom (cycleLinear f K i) ≫ (eta f K hK).d i (i + 1) = 0 := by
  rw [eta_d]
  ext x
  apply Subtype.ext
  change divideLinear f K i (hK.degree (i + 1)) (cycleLinear f K i x) = 0
  apply (hK.degree (i + 1)).right_eq_zero_of_smul
  rw [divide_spec]
  exact congrArg (fun g : K.cycles i ⟶ K.X (i + 1) ↦ g x) (K.iCycles_d i (i + 1))

/-- The cycle map from an object of the canonical regular domain to its integer-indexed eta
complex. -/
@[stacks 0F7P "cycle map into the integer eta complex"]
noncomputable def cyclesMap (f : A) (K : Domain f) (i : ℤ) :
    K.obj.cycles i ⟶ ((functor f).obj K).cycles i :=
  ((functor f).obj K).liftCycles'
    (ModuleCat.ofHom (cycleLinear f K.obj i)) (i + 1) (rel_succ i)
    (cycle_comp_d f K.obj K.property i)

/-- The cycle-level map into eta homology. -/
@[stacks 0F7P "cycle map into integer eta homology"]
noncomputable def cyclesToHomology (f : A) (K : Domain f) (i : ℤ) :
    K.obj.cycles i ⟶ ((functor f).obj K).homology i :=
  cyclesMap f K i ≫ ((functor f).obj K).homologyπ i

/-- In divided coordinates, the eta cycle inclusion preserves the underlying element. -/
private theorem cyclesMap_i_apply (f : A) (K : Domain f) (i : ℤ)
    (x : K.obj.cycles i) :
    (((functor f).obj K).iCycles i (cyclesMap f K i x)).1 = (K.obj.iCycles i) x := by
  have h : cyclesMap f K i ≫ ((functor f).obj K).iCycles i =
      ModuleCat.ofHom (cycleLinear f K.obj i) := by
    exact ((functor f).obj K).liftCycles_i (ModuleCat.ofHom (cycleLinear f K.obj i))
      (i + 1) ((ComplexShape.up ℤ).next_eq' (rel_succ i))
      (cycle_comp_d f K.obj K.property i)
  exact congrArg (fun g : K.obj.cycles i ⟶ ((functor f).obj K).X i ↦ (g x).1) h

/-- A cycle has zero homology class precisely when its underlying element is a boundary. -/
private theorem homologyπ_eq_zero_iff (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (i : ℤ) (x : K.cycles i) :
    K.homologyπ i x = 0 ↔
      ∃ y : K.X ((ComplexShape.up ℤ).prev i),
        K.d ((ComplexShape.up ℤ).prev i) i y = K.iCycles i x := by
  have hi := (ModuleCat.mono_iff_injective (K.homologyι i)).mp inferInstance
  rw [← hi.eq_iff, map_zero]
  change (K.homologyπ i ≫ K.homologyι i) x = 0 ↔ _
  rw [K.homology_π_ι]
  exact (K.sc i).moduleCat_pOpcycles_eq_zero_iff ((K.iCycles i) x)

/-- Boundaries of the underlying complex map to zero in eta homology. -/
theorem boundaries_vanish (f : A) (K : Domain f) (i : ℤ) :
    (K.obj.sc i).toCycles ≫ cyclesToHomology f K i = 0 := by
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, (sub_add_cancel i 1).symm⟩
  have hp : (ComplexShape.up ℤ).prev (j + 1) = j :=
    (ComplexShape.up ℤ).prev_eq' (rel_succ j)
  change K.obj.toCycles ((ComplexShape.up ℤ).prev (j + 1)) (j + 1) ≫
    cyclesToHomology f K (j + 1) = 0
  rw [hp]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((functor f).obj K).homologyπ (j + 1)
    (cyclesMap f K (j + 1) (K.obj.toCycles j (j + 1) x)) = 0
  apply (homologyπ_eq_zero_iff _ _ _).2
  rw [hp]
  have hb : f • x ∈ term f K.obj j := by
    refine ⟨K.obj.d j (j + 1) x, ?_⟩
    exact (map_smul (K.obj.d j (j + 1)).hom f x).symm
  refine ⟨⟨f • x, hb⟩, ?_⟩
  change (eta f K.obj K.property).d j (j + 1) ⟨f • x, hb⟩ = _
  rw [eta_d]
  apply Subtype.ext
  rw [cyclesMap_i_apply]
  change divideLinear f K.obj j (K.property.degree (j + 1)) ⟨f • x, hb⟩ =
    (K.obj.iCycles (j + 1)) (K.obj.toCycles j (j + 1) x)
  apply K.property.degree (j + 1)
  change f • divideLinear f K.obj j (K.property.degree (j + 1)) ⟨f • x, hb⟩ =
    f • (K.obj.iCycles (j + 1)) (K.obj.toCycles j (j + 1) x)
  rw [divide_spec, map_smul]
  exact congrArg (fun y ↦ f • y)
    (congrArg (fun g : K.obj.X j ⟶ K.obj.X (j + 1) ↦ g x)
      (K.obj.toCycles_i j (j + 1))).symm

/-- The map on homology induced by the cycle inclusion. -/
@[stacks 0F7P "homology map induced by the eta cycle inclusion"]
noncomputable def homologyMap (f : A) (K : Domain f) (i : ℤ) :
    K.obj.homology i ⟶ ((functor f).obj K).homology i :=
  (K.obj.sc i).descHomology (cyclesToHomology f K i) (boundaries_vanish f K i)

/-- The homology map is characterized on cycle representatives. -/
theorem homologyπ_comp_homologyMap
    (f : A) (K : Domain f) (i : ℤ) :
    K.obj.homologyπ i ≫ homologyMap f K i = cyclesToHomology f K i := by
  exact (K.obj.sc i).π_descHomology _ _

/-- The integer eta homology map is natural on the canonical regular domain. -/
theorem homologyMap_naturality
    (f : A) {K L : Domain f} (φ : K ⟶ L) (i : ℤ) :
    homologyMap f K i ≫ HomologicalComplex.homologyMap ((functor f).map φ) i =
      HomologicalComplex.homologyMap φ.hom i ≫ homologyMap f L i := by
  have hc : cyclesMap f K i ≫ HomologicalComplex.cyclesMap ((functor f).map φ) i =
      HomologicalComplex.cyclesMap φ.hom i ≫ cyclesMap f L i := by
    apply (cancel_mono (((functor f).obj L).iCycles i)).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i, cyclesMap,
      HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change φ.hom.f i ((K.obj.iCycles i) x) =
      (L.obj.iCycles i) (HomologicalComplex.cyclesMap φ.hom i x)
    exact (congrArg (fun g : K.obj.cycles i ⟶ L.obj.X i ↦ g x)
      (HomologicalComplex.cyclesMap_i φ.hom i)).symm
  apply (cancel_epi (K.obj.homologyπ i)).1
  rw [← Category.assoc, homologyπ_comp_homologyMap,
    HomologicalComplex.homologyπ_naturality_assoc, homologyπ_comp_homologyMap]
  simpa only [cyclesToHomology, Category.assoc,
    HomologicalComplex.homologyπ_naturality] using
    congrArg (fun g ↦ g ≫ ((functor f).obj L).homologyπ i) hc

/-- Evaluation of the homology comparison on a cycle representative. -/
private theorem homologyMap_homologyπ_apply (f : A) (K : Domain f) (i : ℤ)
    (x : K.obj.cycles i) :
    homologyMap f K i (K.obj.homologyπ i x) =
      ((functor f).obj K).homologyπ i (cyclesMap f K i x) := by
  exact congrArg (fun g : K.obj.cycles i ⟶ ((functor f).obj K).homology i ↦ g x)
    (homologyπ_comp_homologyMap f K i)

/-- An element killed by the outgoing differential determines a cycle. -/
private theorem exists_cycle (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (x : K.X i) (hx : K.d i (i + 1) x = 0) :
    ∃ z : K.cycles i, K.iCycles i z = x := by
  have hx' : (K.sc i).g x = 0 := by
    change K.d i ((ComplexShape.up ℤ).next i) x = 0
    rw [(ComplexShape.up ℤ).next_eq' (rel_succ i)]
    exact hx
  exact ⟨(K.sc i).cyclesMk x hx', (K.sc i).i_cyclesMk x hx'⟩

/-- Termwise `f`-regularity makes homology `f`-torsion map to zero under the eta comparison. -/
theorem torsionBy_le_ker
    (f : A) (K : Domain f) (i : ℤ) :
    Submodule.torsionBy A (K.obj.homology i) f ≤
      LinearMap.ker (homologyMap f K i).hom := by
  intro x hx
  change homologyMap f K i x = 0
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.obj.homologyπ i)).mp inferInstance x
  change f • K.obj.homologyπ i z = 0 at hx
  rw [homologyMap_homologyπ_apply]
  have hfz : K.obj.homologyπ i (f • z) = 0 := by simpa only [map_smul] using hx
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, (sub_add_cancel i 1).symm⟩
  have hp : (ComplexShape.up ℤ).prev (j + 1) = j :=
    (ComplexShape.up ℤ).prev_eq' (rel_succ j)
  rw [homologyπ_eq_zero_iff, hp] at hfz
  obtain ⟨y, hy⟩ := hfz
  apply (homologyπ_eq_zero_iff _ _ _).2
  rw [hp]
  have hb : y ∈ term f K.obj j := by
    refine ⟨(K.obj.iCycles (j + 1)) z, ?_⟩
    exact (hy.trans (map_smul (K.obj.iCycles (j + 1)).hom f z)).symm
  refine ⟨⟨y, hb⟩, ?_⟩
  change (eta f K.obj K.property).d j (j + 1) ⟨y, hb⟩ = _
  rw [eta_d]
  apply Subtype.ext
  rw [cyclesMap_i_apply]
  change divideLinear f K.obj j (K.property.degree (j + 1)) ⟨y, hb⟩ =
    (K.obj.iCycles (j + 1)) z
  apply K.property.degree (j + 1)
  change f • divideLinear f K.obj j (K.property.degree (j + 1)) ⟨y, hb⟩ =
    f • (K.obj.iCycles (j + 1)) z
  rw [divide_spec, hy, map_smul]

/-- An eta boundary represents an `f`-torsion class in the original complex. -/
private theorem ker_homologyMap_le_torsionBy (f : A) (K : Domain f) (i : ℤ) :
    LinearMap.ker (homologyMap f K i).hom ≤
      Submodule.torsionBy A (K.obj.homology i) f := by
  intro x hx
  change f • x = 0
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.obj.homologyπ i)).mp inferInstance x
  change homologyMap f K i (K.obj.homologyπ i z) = 0 at hx
  rw [homologyMap_homologyπ_apply] at hx
  obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, (sub_add_cancel i 1).symm⟩
  have hp : (ComplexShape.up ℤ).prev (j + 1) = j :=
    (ComplexShape.up ℤ).prev_eq' (rel_succ j)
  rw [homologyπ_eq_zero_iff, hp] at hx
  obtain ⟨y, hy⟩ := hx
  have he : K.obj.d j (j + 1) y.1 = f • (K.obj.iCycles (j + 1)) z := by
    change (eta f K.obj K.property).d j (j + 1) y = _ at hy
    rw [eta_d] at hy
    have hy' : divideLinear f K.obj j (K.property.degree (j + 1)) y =
        (K.obj.iCycles (j + 1)) z :=
      (congrArg (fun q : ((functor f).obj K).X (j + 1) ↦ q.1) hy).trans
        (cyclesMap_i_apply f K (j + 1) z)
    rw [← divide_spec f K.obj j (K.property.degree (j + 1)) y, hy']
  have hfz : f • z = K.obj.toCycles j (j + 1) y.1 := by
    apply (ModuleCat.mono_iff_injective (K.obj.iCycles (j + 1))).mp inferInstance
    rw [map_smul]
    exact he.symm.trans
      (congrArg (fun g : K.obj.X j ⟶ K.obj.X (j + 1) ↦ g y.1)
        (K.obj.toCycles_i j (j + 1))).symm
  rw [← map_smul, hfz]
  exact congrArg (fun g : K.obj.X j ⟶ K.obj.homology (j + 1) ↦ g y.1)
    (K.obj.toCycles_comp_homologyπ j (j + 1))

/-- The canonical quotient comparison for an integer-indexed regular complex. -/
@[stacks 0F7P "integer-indexed Berthelot-Ogus eta homology comparison map"]
noncomputable def comparison (f : A) (K : Domain f) (i : ℤ) :
    ((K.obj.homology i) ⧸ Submodule.torsionBy A (K.obj.homology i) f) →ₗ[A]
      ((functor f).obj K).homology i :=
  (Submodule.torsionBy A (K.obj.homology i) f).liftQ
    (homologyMap f K i).hom
    (torsionBy_le_ker f K i)

/-- The quotient comparison sends a representative to its eta homology class. -/
theorem comparison_mk
    (f : A) (K : Domain f) (i : ℤ) (x : K.obj.homology i) :
    comparison f K i (Submodule.Quotient.mk x) = (homologyMap f K i).hom x := rfl

/-- The integer-indexed eta comparison is bijective on a termwise regular complex. -/
theorem comparison_bijective (f : A) (K : Domain f) (i : ℤ) :
    Function.Bijective (comparison f K i) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_homologyMap_le_torsionBy f K i)
  · intro x
    obtain ⟨z, rfl⟩ :=
      (ModuleCat.epi_iff_surjective (((functor f).obj K).homologyπ i)).mp inferInstance x
    let t : term f K.obj i := ((functor f).obj K).iCycles i z
    have hd : K.obj.d i (i + 1) t.1 = 0 := by
      have hc := congrArg
        (fun g : ((functor f).obj K).cycles i ⟶ ((functor f).obj K).X (i + 1) ↦ g z)
        (((functor f).obj K).iCycles_d i (i + 1))
      change (eta f K.obj K.property).d i (i + 1) t = 0 at hc
      rw [eta_d] at hc
      have hc' : divideLinear f K.obj i (K.property.degree (i + 1)) t = 0 :=
        congrArg (fun q : ((functor f).obj K).X (i + 1) ↦ q.1) hc
      rw [← divide_spec f K.obj i (K.property.degree (i + 1)) t, hc', smul_zero]
    obtain ⟨w, hw⟩ := exists_cycle K.obj i t.1 hd
    have hz : cyclesMap f K i w = z := by
      apply (ModuleCat.mono_iff_injective (((functor f).obj K).iCycles i)).mp inferInstance
      apply Subtype.ext
      rw [cyclesMap_i_apply, hw]
    refine ⟨Submodule.Quotient.mk (K.obj.homologyπ i w), ?_⟩
    rw [comparison_mk]
    change homologyMap f K i (K.obj.homologyπ i w) = ((functor f).obj K).homologyπ i z
    rw [homologyMap_homologyπ_apply, hz]

/-- The quotient comparison for a raw complex equipped with an explicit termwise regularity
proof.  Canonical downstream developments should use `comparison` on `Domain f`. -/
@[stacks 0F7P "eta homology comparison for an explicitly regular complex"]
noncomputable def comparisonOfRegular
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    ((K.homology i) ⧸ Submodule.torsionBy A (K.homology i) f) →ₗ[A]
      (eta f K hK).homology i :=
  comparison f ⟨K, hK⟩ i

/-- The raw regular-complex bridge is bijective. -/
theorem comparisonOfRegular_bijective
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    Function.Bijective (comparisonOfRegular f K i hK) := by
  exact comparison_bijective f ⟨K, hK⟩ i

/-- Lemma 15.96.2, Tag 0F7P: for a nonzerodivisor `f` and an integer-indexed complex of
`f`-torsion-free modules, the degree-`i` divided-coordinate comparison identifies homology modulo
`f`-torsion with the homology of the Berthelot-Ogus eta complex. -/
@[stacks 0F7P "Berthelot-Ogus eta homology comparison"]
theorem comparison_bijective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseTorsionFree f K) :
    Function.Bijective (comparisonOfRegular f K i hK) := by
  exact comparisonOfRegular_bijective f K i hK

end CochainComplex.BerthelotOgus.Int
