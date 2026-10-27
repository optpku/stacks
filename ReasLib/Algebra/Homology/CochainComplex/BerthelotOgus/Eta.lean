/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.HomologicalComplex.Termwise.Regular

/-!
# The Berthelot-Ogus eta operator on nonnegative cochain complexes

This file owns the nonnegative-degree model of the Berthelot-Ogus operator.  The terms are the
submodules

`f ^ n K.X n ∩ d⁻¹(f ^ (n + 1) K.X (n + 1))`,

so no choice of representatives or extension to negative powers is built into the construction.
The comparison on cohomology is induced by multiplication by `f ^ n`.
@stack 0F7P
-/

@[expose] public section

open CategoryTheory
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Nat

variable {A : Type u} [CommRing A]

/-- The nonnegative-cochain specialization of shape-independent termwise scalar regularity. -/
@[stacks 0F7P "termwise regular nonnegative eta complexes"]
abbrev IsTermwiseTorsionFree (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) : Prop :=
  K.IsTermwiseSMulRegular f

/-- Termwise `f`-torsion-freeness is exactly degreewise `f`-regularity. -/
theorem isTermwiseTorsionFree_iff (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) :
    IsTermwiseTorsionFree f K ↔ ∀ n : ℕ, IsSMulRegular (K.X n) f := Iff.rfl

/-- The degree-`n` term of the Berthelot-Ogus complex `η_f K`. -/
@[stacks 0F7P "degree term of the Berthelot-Ogus eta complex"]
def term (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Submodule A (K.X n) :=
  LinearMap.range (LinearMap.lsmul A (K.X n) (f ^ n)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (K.X (n + 1)) (f ^ (n + 1)))).comap (K.d n (n + 1)).hom

/-- The differential of `K` sends the degree-`n` eta term into the next eta term. -/
theorem d_mem (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : term f K n) : K.d n (n + 1) x ∈ term f K (n + 1) := by
  refine ⟨x.2.2, ?_⟩
  have hz : K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) x.1) = 0 := by
    exact congrArg (fun g : K.X n ⟶ K.X (n + 1 + 1) ↦ g x.1)
      (K.d_comp_d n (n + 1) (n + 1 + 1))
  change K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) x.1) ∈
    LinearMap.range (LinearMap.lsmul A (K.X (n + 1 + 1)) (f ^ (n + 1 + 1)))
  rw [hz]
  exact Submodule.zero_mem _

/-- The differential of `η_f K` in degree `n`, obtained by restricting the differential of
`K`. -/
@[stacks 0F7P "differential of the nonnegative eta complex"]
def dLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    term f K n →ₗ[A] term f K (n + 1) :=
  ((K.d n (n + 1)).hom.comp (term f K n).subtype).codRestrict
    (term f K (n + 1)) (d_mem f K n)

/-- Two successive restricted eta differentials compose to zero. -/
theorem d_comp_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ModuleCat.ofHom (dLinear f K n) ≫ ModuleCat.ofHom (dLinear f K (n + 1)) = 0 := by
  ext x
  change K.d (n + 1) (n + 1 + 1) (K.d n (n + 1) x.1) = 0
  exact congrArg (fun g : K.X n ⟶ K.X (n + 1 + 1) ↦ g x.1)
    (K.d_comp_d n (n + 1) (n + 1 + 1))

/-- The Berthelot-Ogus eta complex of a nonnegative cochain complex. -/
@[stacks 0F7P "Berthelot-Ogus eta complex"]
def eta (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) :
    CochainComplex (ModuleCat.{v} A) ℕ :=
  CochainComplex.of
    (fun n ↦ ModuleCat.of A (term f K n))
    (fun n ↦ ModuleCat.ofHom (dLinear f K n))
    (fun n ↦ d_comp_d f K n)

/-- The degree objects of the eta complex are its defining submodules. -/
@[simp]
theorem eta_X (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (eta f K).X n = ModuleCat.of A (term f K n) := rfl

/-- The eta differential in consecutive degrees is the restricted ambient differential. -/
@[simp]
theorem eta_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (eta f K).d n (n + 1) = ModuleCat.ofHom (dLinear f K n) := by
  exact CochainComplex.of_d (fun n ↦ ModuleCat.of A (term f K n))
    (fun n ↦ ModuleCat.ofHom (dLinear f K n)) n

scoped[BerthelotOgus] notation "η[" f "] " K:arg =>
  CochainComplex.BerthelotOgus.Nat.eta f K

/-- A cochain map preserves the defining degree submodules of the eta construction. -/
theorem map_mem (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (n : ℕ) (x : term f K n) : φ.f n x ∈ term f L n := by
  rcases x.2.1 with ⟨y, hy⟩
  rcases x.2.2 with ⟨z, hz⟩
  refine ⟨⟨φ.f n y, ?_⟩, ⟨φ.f (n + 1) z, ?_⟩⟩
  · change (f ^ n) • φ.f n y = φ.f n x.1
    rw [← map_smul]
    exact congrArg (φ.f n) hy
  · change (f ^ (n + 1)) • φ.f (n + 1) z = L.d n (n + 1) (φ.f n x.1)
    rw [← map_smul]
    calc
      φ.f (n + 1) ((f ^ (n + 1)) • z) = φ.f (n + 1) (K.d n (n + 1) x.1) :=
        congrArg (φ.f (n + 1)) hz
      _ = L.d n (n + 1) (φ.f n x.1) :=
        (congrArg (fun g : K.X n ⟶ L.X (n + 1) ↦ g x.1) (φ.comm n (n + 1))).symm

/-- The degree-`n` linear map induced by a cochain map on eta terms. -/
@[stacks 0F7P "degreewise map on nonnegative eta terms"]
def mapLinear (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (n : ℕ) : term f K n →ₗ[A] term f L n :=
  ((φ.f n).hom.comp (term f K n).subtype).codRestrict (term f L n) (map_mem f φ n)

/-- The induced maps on eta terms commute with the restricted differentials. -/
theorem map_comm (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    ModuleCat.ofHom (mapLinear f φ i) ≫ (eta f L).d i j =
      (eta f K).d i j ≫ ModuleCat.ofHom (mapLinear f φ j) := by
  obtain rfl : i + 1 = j := hij
  rw [eta_d, eta_d]
  ext x
  apply Subtype.ext
  change L.d i (i + 1) (φ.f i x.1) = φ.f (i + 1) (K.d i (i + 1) x.1)
  exact congrArg (fun g : K.X i ⟶ L.X (i + 1) ↦ g x.1) (φ.comm i (i + 1))

/-- The morphism `η_f K ⟶ η_f L` induced by a cochain map `K ⟶ L`. -/
@[stacks 0F7P "map on nonnegative eta complexes"]
def map (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L) :
    eta f K ⟶ eta f L where
  f n := ModuleCat.ofHom (mapLinear f φ n)
  comm' i j hij := map_comm f φ i j hij

/-- The degree components of the induced eta map are the restricted ambient maps. -/
@[simp]
theorem map_f (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (n : ℕ) : (map f φ).f n = ModuleCat.ofHom (mapLinear f φ n) := rfl

/-- The eta construction sends identity cochain maps to identity maps. -/
@[simp]
theorem map_id (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) :
    map f (𝟙 K) = 𝟙 (eta f K) := by
  ext n x
  rfl

/-- The eta construction preserves composition of cochain maps. -/
@[simp]
theorem map_comp (f : A) {K L M : CochainComplex (ModuleCat.{v} A) ℕ}
    (φ : K ⟶ L) (ψ : L ⟶ M) : map f (φ ≫ ψ) = map f φ ≫ map f ψ := by
  ext n x
  rfl

/-- The eta construction preserves addition of cochain maps. -/
theorem map_add (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ}
    (φ ψ : K ⟶ L) : map f (φ + ψ) = map f φ + map f ψ := by
  ext n x
  rfl

/-- The functorial Berthelot-Ogus eta construction on nonnegative cochain complexes. -/
@[stacks 0F7P "nonnegative Berthelot-Ogus eta functor"]
def functor (f : A) :
    CochainComplex (ModuleCat.{v} A) ℕ ⥤ CochainComplex (ModuleCat.{v} A) ℕ where
  obj K := eta f K
  map φ := map f φ
  map_id K := map_id f K
  map_comp φ ψ := map_comp f φ ψ

/-- The object part of the eta functor is the eta complex. -/
@[simp]
theorem functor_obj (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) :
    (functor f).obj K = eta f K := rfl

/-- The morphism part of the eta functor is the restricted ambient cochain map. -/
@[simp]
theorem functor_map (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L) :
    (functor f).map φ = map f φ := rfl

/-- The eta functor is additive. -/
@[stacks 0F7P "additivity of the nonnegative eta functor", instance]
instance functor_additive (f : A) : (functor f).Additive where
  map_add := map_add f _ _

/-- The eta complex of a termwise `f`-torsion-free complex is again termwise
`f`-torsion-free. -/
theorem eta_isTermwiseTorsionFree
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree f K) : IsTermwiseTorsionFree f (eta f K) := by
  intro n
  exact IsSMulRegular.submodule (term f K n) f (hK n)

/-- Consecutive degrees are related by the cochain complex shape on `ℕ`. -/
theorem rel_succ (n : ℕ) : (ComplexShape.up ℕ).Rel n (n + 1) := rfl

/-- Multiplication by `f ^ n` sends a cycle of `K` into the degree-`n` eta term. -/
theorem cycleScale_mem (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : K.cycles n) :
    ((LinearMap.lsmul A (K.X n) (f ^ n)).comp (K.iCycles n).hom) x ∈ term f K n := by
  refine ⟨⟨(K.iCycles n) x, rfl⟩, ?_⟩
  have hz : K.d n (n + 1) ((K.iCycles n) x) = 0 :=
    congrArg (fun g : K.cycles n ⟶ K.X (n + 1) ↦ g x) (K.iCycles_d n (n + 1))
  change K.d n (n + 1) ((f ^ n) • (K.iCycles n) x) ∈
    LinearMap.range (LinearMap.lsmul A (K.X (n + 1)) (f ^ (n + 1)))
  rw [map_smul, hz, smul_zero]
  exact Submodule.zero_mem _

/-- Multiplication by `f ^ n` on cycles, with codomain restricted to the eta term. -/
@[stacks 0F7P "scaled cycle map into an eta term"]
def cycleScaleLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    K.cycles n →ₗ[A] term f K n :=
  ((LinearMap.lsmul A (K.X n) (f ^ n)).comp (K.iCycles n).hom).codRestrict
    (term f K n) (cycleScale_mem f K n)

/-- The scaled cycle map has zero composite with the next eta differential. -/
theorem cycleScale_comp_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ModuleCat.ofHom (cycleScaleLinear f K n) ≫ (eta f K).d n (n + 1) = 0 := by
  rw [eta_d]
  ext x
  apply Subtype.ext
  change K.d n (n + 1) ((f ^ n) • (K.iCycles n) x) = 0
  rw [map_smul]
  have hz : K.d n (n + 1) ((K.iCycles n) x) = 0 :=
    congrArg (fun g : K.cycles n ⟶ K.X (n + 1) ↦ g x) (K.iCycles_d n (n + 1))
  rw [hz, smul_zero]

/-- The cycle map into `η_f K` induced by multiplication by `f ^ n`. -/
@[stacks 0F7P "cycle map into the nonnegative eta complex"]
noncomputable def cyclesMap (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    K.cycles n ⟶ (eta f K).cycles n :=
  (eta f K).liftCycles'
    (ModuleCat.ofHom (cycleScaleLinear f K n)) (n + 1) (rel_succ n)
    (cycleScale_comp_d f K n)

/-- The map from cycles of `K` to degree-`n` homology of `η_f K`. -/
@[stacks 0F7P "cycles-to-homology map for eta"]
noncomputable def cyclesToHomology
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    K.cycles n ⟶ (eta f K).homology n :=
  cyclesMap f K n ≫ (eta f K).homologyπ n

/-- On underlying elements, the eta cycle map is multiplication by the degree power. -/
private theorem cyclesMap_i_apply (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) (x : K.cycles n) :
    ((eta f K).iCycles n (cyclesMap f K n x)).1 = (f ^ n) • (K.iCycles n) x := by
  have h : cyclesMap f K n ≫ (eta f K).iCycles n =
      ModuleCat.ofHom (cycleScaleLinear f K n) := by
    exact (eta f K).liftCycles_i (ModuleCat.ofHom (cycleScaleLinear f K n)) (n + 1)
      ((ComplexShape.up ℕ).next_eq' (rel_succ n)) (cycleScale_comp_d f K n)
  exact congrArg (fun g : K.cycles n ⟶ (eta f K).X n ↦ (g x).1) h

/-- A homology class vanishes exactly when its cycle representative is a boundary. -/
private theorem homologyπ_eq_zero_iff (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) (x : K.cycles n) :
    K.homologyπ n x = 0 ↔
      ∃ y : K.X ((ComplexShape.up ℕ).prev n),
        K.d ((ComplexShape.up ℕ).prev n) n y = K.iCycles n x := by
  have hi := (ModuleCat.mono_iff_injective (K.homologyι n)).mp inferInstance
  rw [← hi.eq_iff, map_zero]
  change (K.homologyπ n ≫ K.homologyι n) x = 0 ↔ _
  rw [K.homology_π_ι]
  exact (K.sc n).moduleCat_pOpcycles_eq_zero_iff ((K.iCycles n) x)

/-- The scaled cycle map annihilates boundaries of `K`. -/
theorem boundaries_vanish (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (K.sc n).toCycles ≫ cyclesToHomology f K n = 0 := by
  cases n with
  | zero =>
    change K.toCycles ((ComplexShape.up ℕ).prev 0) 0 ≫ cyclesToHomology f K 0 = 0
    rw [K.toCycles_eq_zero (i := (ComplexShape.up ℕ).prev 0) (j := 0) (by
      intro h
      exact Nat.add_one_ne_zero _ h)]
    simp
  | succ n =>
    have hp : (ComplexShape.up ℕ).prev (n + 1) = n :=
      (ComplexShape.up ℕ).prev_eq' (rel_succ n)
    change K.toCycles ((ComplexShape.up ℕ).prev (n + 1)) (n + 1) ≫
      cyclesToHomology f K (n + 1) = 0
    rw [hp]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (eta f K).homologyπ (n + 1)
      (cyclesMap f K (n + 1) (K.toCycles n (n + 1) x)) = 0
    apply (homologyπ_eq_zero_iff _ _ _).2
    rw [hp]
    have hb : (f ^ (n + 1)) • x ∈ term f K n := by
      constructor
      · refine ⟨f • x, ?_⟩
        change (f ^ n) • (f • x) = (f ^ (n + 1)) • x
        rw [pow_succ, mul_smul]
      · exact ⟨K.d n (n + 1) x, by simp [map_smul]⟩
    refine ⟨⟨(f ^ (n + 1)) • x, hb⟩, ?_⟩
    rw [eta_d]
    apply Subtype.ext
    rw [cyclesMap_i_apply]
    change K.d n (n + 1) ((f ^ (n + 1)) • x) =
      (f ^ (n + 1)) • (K.iCycles (n + 1)) (K.toCycles n (n + 1) x)
    rw [map_smul]
    exact congrArg (fun y ↦ (f ^ (n + 1)) • y)
      (congrArg (fun g : K.X n ⟶ K.X (n + 1) ↦ g x)
        (K.toCycles_i n (n + 1))).symm

/-- Multiplication by `f ^ n` induces a map from degree-`n` homology of `K` to degree-`n`
homology of `η_f K`. -/
@[stacks 0F7P "homology map for the nonnegative eta complex"]
noncomputable def homologyMap
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    K.homology n ⟶ (eta f K).homology n :=
  (K.sc n).descHomology (cyclesToHomology f K n) (boundaries_vanish f K n)

/-- The homology map is characterized on cycle representatives by multiplication by `f ^ n`. -/
theorem homologyπ_comp_homologyMap
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    K.homologyπ n ≫ homologyMap f K n = cyclesToHomology f K n := by
  exact (K.sc n).π_descHomology _ _

/-- The homology comparison is natural with respect to cochain maps. -/
theorem homologyMap_naturality
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L) (n : ℕ) :
    homologyMap f K n ≫ HomologicalComplex.homologyMap (map f φ) n =
      HomologicalComplex.homologyMap φ n ≫ homologyMap f L n := by
  have hc : cyclesMap f K n ≫ HomologicalComplex.cyclesMap (map f φ) n =
      HomologicalComplex.cyclesMap φ n ≫ cyclesMap f L n := by
    apply (cancel_mono ((eta f L).iCycles n)).1
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i, cyclesMap,
      HomologicalComplex.liftCycles_i_assoc, HomologicalComplex.liftCycles_i]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change φ.f n ((f ^ n) • (K.iCycles n) x) =
      (f ^ n) • (L.iCycles n) (HomologicalComplex.cyclesMap φ n x)
    have hx : (L.iCycles n) (HomologicalComplex.cyclesMap φ n x) =
        φ.f n ((K.iCycles n) x) :=
      congrArg (fun g : K.cycles n ⟶ L.X n ↦ g x)
        (HomologicalComplex.cyclesMap_i φ n)
    rw [hx, map_smul]
  apply (cancel_epi (K.homologyπ n)).1
  rw [← Category.assoc, homologyπ_comp_homologyMap,
    HomologicalComplex.homologyπ_naturality_assoc, homologyπ_comp_homologyMap]
  simpa only [cyclesToHomology, Category.assoc,
    HomologicalComplex.homologyπ_naturality] using
    congrArg (fun g ↦ g ≫ (eta f L).homologyπ n) hc

/-- The induced homology map evaluates on cycle representatives by scaling. -/
private theorem homologyMap_homologyπ_apply (f : A)
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) (x : K.cycles n) :
    homologyMap f K n (K.homologyπ n x) =
      (eta f K).homologyπ n (cyclesMap f K n x) := by
  exact congrArg (fun g : K.cycles n ⟶ (eta f K).homology n ↦ g x)
    (homologyπ_comp_homologyMap f K n)

/-- An element killed by the outgoing differential has a cycle representative. -/
private theorem exists_cycle (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (n : ℕ) (x : K.X n) (hx : K.d n (n + 1) x = 0) :
    ∃ z : K.cycles n, K.iCycles n z = x := by
  have hx' : (K.sc n).g x = 0 := by
    change K.d n ((ComplexShape.up ℕ).next n) x = 0
    rw [(ComplexShape.up ℕ).next_eq' (rel_succ n)]
    exact hx
  exact ⟨(K.sc n).cyclesMk x hx', (K.sc n).i_cyclesMk x hx'⟩

/-- For a termwise `f`-torsion-free complex, `f`-torsion in homology lies in the kernel of the
eta homology map. -/
theorem torsionBy_le_ker (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hK : IsTermwiseTorsionFree f K) :
    Submodule.torsionBy A (K.homology n) f ≤ LinearMap.ker (homologyMap f K n).hom := by
  intro x hx
  change homologyMap f K n x = 0
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance x
  change f • K.homologyπ n z = 0 at hx
  rw [homologyMap_homologyπ_apply]
  have hfz : K.homologyπ n (f • z) = 0 := by simpa only [map_smul] using hx
  cases n with
  | zero =>
    obtain ⟨y, hy⟩ := (homologyπ_eq_zero_iff K 0 (f • z)).mp hfz
    have hd : K.d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
      K.shape _ _ (by intro h; exact Nat.add_one_ne_zero _ h)
    rw [hd, map_smul] at hy
    have hz : z = 0 := by
      apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
      rw [map_zero]
      exact (hK 0).right_eq_zero_of_smul hy.symm
    simp only [hz, map_zero]
  | succ n =>
    have hp : (ComplexShape.up ℕ).prev (n + 1) = n :=
      (ComplexShape.up ℕ).prev_eq' (rel_succ n)
    rw [homologyπ_eq_zero_iff, hp] at hfz
    obtain ⟨y, hy⟩ := hfz
    apply (homologyπ_eq_zero_iff _ _ _).2
    rw [hp]
    have hb : (f ^ n) • y ∈ term f K n := by
      refine ⟨⟨y, rfl⟩, ⟨(K.iCycles (n + 1)) z, ?_⟩⟩
      change (f ^ (n + 1)) • (K.iCycles (n + 1)) z =
        K.d n (n + 1) ((f ^ n) • y)
      rw [map_smul, hy, map_smul, pow_succ, mul_smul]
    refine ⟨⟨(f ^ n) • y, hb⟩, ?_⟩
    rw [eta_d]
    apply Subtype.ext
    rw [cyclesMap_i_apply]
    change K.d n (n + 1) ((f ^ n) • y) =
      (f ^ (n + 1)) • (K.iCycles (n + 1)) z
    rw [map_smul, hy, map_smul, pow_succ, mul_smul]

/-- Only `f`-torsion can vanish under the scaled homology map. -/
private theorem ker_homologyMap_le_torsionBy (f : A)
    (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hK : IsTermwiseTorsionFree f K) :
    LinearMap.ker (homologyMap f K n).hom ≤ Submodule.torsionBy A (K.homology n) f := by
  intro x hx
  change f • x = 0
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ n)).mp inferInstance x
  change homologyMap f K n (K.homologyπ n z) = 0 at hx
  rw [homologyMap_homologyπ_apply] at hx
  cases n with
  | zero =>
    obtain ⟨y, hy⟩ := (homologyπ_eq_zero_iff _ _ _).mp hx
    have hd : (eta f K).d ((ComplexShape.up ℕ).prev 0) 0 = 0 :=
      (eta f K).shape _ _ (by intro h; exact Nat.add_one_ne_zero _ h)
    rw [hd] at hy
    have hzeta : ((eta f K).iCycles 0 (cyclesMap f K 0 z)).1 = 0 :=
      (congrArg (fun q : (eta f K).X 0 ↦ q.1) hy).symm
    rw [cyclesMap_i_apply, pow_zero, one_smul] at hzeta
    have hz : z = 0 := by
      apply (ModuleCat.mono_iff_injective (K.iCycles 0)).mp inferInstance
      simpa only [map_zero] using hzeta
    simp only [hz, map_zero, smul_zero]
  | succ n =>
    have hp : (ComplexShape.up ℕ).prev (n + 1) = n :=
      (ComplexShape.up ℕ).prev_eq' (rel_succ n)
    rw [homologyπ_eq_zero_iff, hp] at hx
    obtain ⟨y, hy⟩ := hx
    rcases y.2.1 with ⟨w, hw⟩
    rw [eta_d] at hy
    have he : K.d n (n + 1) y.1 =
        (f ^ (n + 1)) • (K.iCycles (n + 1)) z := by
      exact (congrArg (fun q : (eta f K).X (n + 1) ↦ q.1) hy).trans
        (cyclesMap_i_apply f K (n + 1) z)
    change (f ^ n) • w = y.1 at hw
    rw [← hw, map_smul, pow_succ, mul_smul] at he
    have hd : K.d n (n + 1) w = f • (K.iCycles (n + 1)) z :=
      ((hK (n + 1)).pow n) he
    have hfz : f • z = K.toCycles n (n + 1) w := by
      apply (ModuleCat.mono_iff_injective (K.iCycles (n + 1))).mp inferInstance
      rw [map_smul]
      exact hd.symm.trans
        (congrArg (fun g : K.X n ⟶ K.X (n + 1) ↦ g w)
          (K.toCycles_i n (n + 1))).symm
    rw [← map_smul, hfz]
    exact congrArg (fun g : K.X n ⟶ K.homology (n + 1) ↦ g w)
      (K.toCycles_comp_homologyπ n (n + 1))

/-- The canonical quotient comparison
`H^n(K) / H^n(K)[f] → H^n(η_f K)` induced by multiplication by `f ^ n`. -/
@[stacks 0F7P "Berthelot-Ogus eta homology comparison map"]
noncomputable def comparison (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hK : IsTermwiseTorsionFree f K) :
    ((K.homology n) ⧸ Submodule.torsionBy A (K.homology n) f) →ₗ[A]
      (eta f K).homology n :=
  (Submodule.torsionBy A (K.homology n) f).liftQ
    (homologyMap f K n).hom (torsionBy_le_ker f K n hK)

/-- The quotient comparison sends the class of a homology element to its eta homology image. -/
theorem comparison_mk (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hK : IsTermwiseTorsionFree f K) (x : K.homology n) :
    comparison f K n hK (Submodule.Quotient.mk x) = (homologyMap f K n).hom x := rfl

/-- The quotient comparison is bijective for a termwise `f`-torsion-free nonnegative complex. -/
theorem comparison_bijective (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hK : IsTermwiseTorsionFree f K) : Function.Bijective (comparison f K n hK) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (ker_homologyMap_le_torsionBy f K n hK)
  · intro x
    obtain ⟨z, rfl⟩ :=
      (ModuleCat.epi_iff_surjective ((eta f K).homologyπ n)).mp inferInstance x
    let t : term f K n := (eta f K).iCycles n z
    rcases t.2.1 with ⟨a, ha⟩
    change (f ^ n) • a = t.1 at ha
    have hd : K.d n (n + 1) t.1 = 0 := by
      have hc := congrArg
        (fun g : (eta f K).cycles n ⟶ (eta f K).X (n + 1) ↦ g z)
        ((eta f K).iCycles_d n (n + 1))
      rw [eta_d] at hc
      exact congrArg (fun q : (eta f K).X (n + 1) ↦ q.1) hc
    have hda : K.d n (n + 1) a = 0 := by
      apply ((hK (n + 1)).pow n).right_eq_zero_of_smul
      rw [← map_smul, ha]
      exact hd
    obtain ⟨w, hw⟩ := exists_cycle K n a hda
    have hz : cyclesMap f K n w = z := by
      apply (ModuleCat.mono_iff_injective ((eta f K).iCycles n)).mp inferInstance
      apply Subtype.ext
      rw [cyclesMap_i_apply, hw]
      exact ha
    refine ⟨Submodule.Quotient.mk (K.homologyπ n w), ?_⟩
    rw [comparison_mk]
    change homologyMap f K n (K.homologyπ n w) = (eta f K).homologyπ n z
    rw [homologyMap_homologyπ_apply, hz]

/-- Lemma 15.96.2, tag `0F7P`: if `f` is a nonzerodivisor and `K` is termwise
`f`-torsion-free, multiplication by `f ^ n` identifies
`H^n(K) / H^n(K)[f]` with `H^n(η_f K)`. -/
@[stacks 0F7P "Berthelot-Ogus eta homology comparison"]
theorem comparison_bijective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseTorsionFree f K) :
    Function.Bijective (comparison f K n hK) := by
  exact comparison_bijective f K n hK

end CochainComplex.BerthelotOgus.Nat
