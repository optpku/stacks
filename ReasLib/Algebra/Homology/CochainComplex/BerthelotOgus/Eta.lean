module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
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
    IsTermwiseTorsionFree f K ↔ ∀ n : ℕ, IsSMulRegular (K.X n) f := sorry

/-- The degree-`n` term of the Berthelot-Ogus complex `η_f K`. -/
@[stacks 0F7P "degree term of the Berthelot-Ogus eta complex"]
def term (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    Submodule A (K.X n) :=
  LinearMap.range (LinearMap.lsmul A (K.X n) (f ^ n)) ⊓
    (LinearMap.range
      (LinearMap.lsmul A (K.X (n + 1)) (f ^ (n + 1)))).comap (K.d n (n + 1)).hom

/-- The differential of `K` sends the degree-`n` eta term into the next eta term. -/
theorem d_mem (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : term f K n) : K.d n (n + 1) x ∈ term f K (n + 1) := sorry

/-- The differential of `η_f K` in degree `n`, obtained by restricting the differential of
`K`. -/
@[stacks 0F7P "differential of the nonnegative eta complex"]
def dLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    term f K n →ₗ[A] term f K (n + 1) :=
  ((K.d n (n + 1)).hom.comp (term f K n).subtype).codRestrict
    (term f K (n + 1)) (d_mem f K n)

/-- Two successive restricted eta differentials compose to zero. -/
theorem d_comp_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ModuleCat.ofHom (dLinear f K n) ≫ ModuleCat.ofHom (dLinear f K (n + 1)) = 0 := sorry

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
    (eta f K).X n = ModuleCat.of A (term f K n) := sorry

/-- The eta differential in consecutive degrees is the restricted ambient differential. -/
@[simp]
theorem eta_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (eta f K).d n (n + 1) = ModuleCat.ofHom (dLinear f K n) := sorry

scoped[BerthelotOgus] notation "η[" f "] " K:arg =>
  CochainComplex.BerthelotOgus.Nat.eta f K

/-- A cochain map preserves the defining degree submodules of the eta construction. -/
theorem map_mem (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (n : ℕ) (x : term f K n) : φ.f n x ∈ term f L n := sorry

/-- The degree-`n` linear map induced by a cochain map on eta terms. -/
@[stacks 0F7P "degreewise map on nonnegative eta terms"]
def mapLinear (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (n : ℕ) : term f K n →ₗ[A] term f L n :=
  ((φ.f n).hom.comp (term f K n).subtype).codRestrict (term f L n) (map_mem f φ n)

/-- The induced maps on eta terms commute with the restricted differentials. -/
theorem map_comm (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (i j : ℕ) (hij : (ComplexShape.up ℕ).Rel i j) :
    ModuleCat.ofHom (mapLinear f φ i) ≫ (eta f L).d i j =
      (eta f K).d i j ≫ ModuleCat.ofHom (mapLinear f φ j) := sorry

/-- The morphism `η_f K ⟶ η_f L` induced by a cochain map `K ⟶ L`. -/
@[stacks 0F7P "map on nonnegative eta complexes"]
def map (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L) :
    eta f K ⟶ eta f L where
  f n := ModuleCat.ofHom (mapLinear f φ n)
  comm' i j hij := map_comm f φ i j hij

/-- The degree components of the induced eta map are the restricted ambient maps. -/
@[simp]
theorem map_f (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L)
    (n : ℕ) : (map f φ).f n = ModuleCat.ofHom (mapLinear f φ n) := sorry

/-- The eta construction sends identity cochain maps to identity maps. -/
@[simp]
theorem map_id (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) :
    map f (𝟙 K) = 𝟙 (eta f K) := sorry

/-- The eta construction preserves composition of cochain maps. -/
@[simp]
theorem map_comp (f : A) {K L M : CochainComplex (ModuleCat.{v} A) ℕ}
    (φ : K ⟶ L) (ψ : L ⟶ M) : map f (φ ≫ ψ) = map f φ ≫ map f ψ := sorry

/-- The eta construction preserves addition of cochain maps. -/
theorem map_add (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ}
    (φ ψ : K ⟶ L) : map f (φ + ψ) = map f φ + map f ψ := sorry

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
    (functor f).obj K = eta f K := sorry

/-- The morphism part of the eta functor is the restricted ambient cochain map. -/
@[simp]
theorem functor_map (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L) :
    (functor f).map φ = map f φ := sorry

/-- The eta functor is additive. -/
@[stacks 0F7P "additivity of the nonnegative eta functor", instance]
instance functor_additive (f : A) : (functor f).Additive := sorry

/-- The eta complex of a termwise `f`-torsion-free complex is again termwise
`f`-torsion-free. -/
theorem eta_isTermwiseTorsionFree
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ)
    (hK : IsTermwiseTorsionFree f K) : IsTermwiseTorsionFree f (eta f K) := sorry

/-- Consecutive degrees are related by the cochain complex shape on `ℕ`. -/
theorem rel_succ (n : ℕ) : (ComplexShape.up ℕ).Rel n (n + 1) := sorry

/-- Multiplication by `f ^ n` sends a cycle of `K` into the degree-`n` eta term. -/
theorem cycleScale_mem (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (x : K.cycles n) :
    ((LinearMap.lsmul A (K.X n) (f ^ n)).comp (K.iCycles n).hom) x ∈ term f K n := sorry

/-- Multiplication by `f ^ n` on cycles, with codomain restricted to the eta term. -/
@[stacks 0F7P "scaled cycle map into an eta term"]
def cycleScaleLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    K.cycles n →ₗ[A] term f K n :=
  ((LinearMap.lsmul A (K.X n) (f ^ n)).comp (K.iCycles n).hom).codRestrict
    (term f K n) (cycleScale_mem f K n)

/-- The scaled cycle map has zero composite with the next eta differential. -/
theorem cycleScale_comp_d (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    ModuleCat.ofHom (cycleScaleLinear f K n) ≫ (eta f K).d n (n + 1) = 0 := sorry

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

/-- The scaled cycle map annihilates boundaries of `K`. -/
theorem boundaries_vanish (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ) :
    (K.sc n).toCycles ≫ cyclesToHomology f K n = 0 := sorry

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
    K.homologyπ n ≫ homologyMap f K n = cyclesToHomology f K n := sorry

/-- The homology comparison is natural with respect to cochain maps. -/
theorem homologyMap_naturality
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℕ} (φ : K ⟶ L) (n : ℕ) :
    homologyMap f K n ≫ HomologicalComplex.homologyMap (map f φ) n =
      HomologicalComplex.homologyMap φ n ≫ homologyMap f L n := sorry

/-- For a termwise `f`-torsion-free complex, `f`-torsion in homology lies in the kernel of the
eta homology map. -/
theorem torsionBy_le_ker (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hK : IsTermwiseTorsionFree f K) :
    Submodule.torsionBy A (K.homology n) f ≤ LinearMap.ker (homologyMap f K n).hom := sorry

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
    comparison f K n hK (Submodule.Quotient.mk x) = (homologyMap f K n).hom x := sorry

/-- The quotient comparison is bijective for a termwise `f`-torsion-free nonnegative complex. -/
theorem comparison_bijective (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hK : IsTermwiseTorsionFree f K) : Function.Bijective (comparison f K n hK) := sorry

/-- Lemma 15.96.2, tag `0F7P`: if `f` is a nonzerodivisor and `K` is termwise
`f`-torsion-free, multiplication by `f ^ n` identifies
`H^n(K) / H^n(K)[f]` with `H^n(η_f K)`. -/
@[stacks 0F7P "Berthelot-Ogus eta homology comparison"]
theorem comparison_bijective_of_nonZeroDivisor
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℕ) (n : ℕ)
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseTorsionFree f K) :
    Function.Bijective (comparison f K n hK) := sorry

end CochainComplex.BerthelotOgus.Nat
