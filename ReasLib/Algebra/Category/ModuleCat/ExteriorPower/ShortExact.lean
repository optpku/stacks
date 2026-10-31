/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Determinant.TwoTerm
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.GradedProjection
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.ExteriorPower.Epi
public import ReasLib.Algebra.Category.ModuleCat.ShortComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped Module.Determinant TensorProduct

noncomputable section

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R]
variable {S : ShortComplex (ModuleCat.{v} R)} {N : ModuleCat.{v} R}

/-- The map from the differential source to the product model of a split short exact row. -/
noncomputable def exteriorComparisonProductLift (s : S.Splitting)
    (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃) :
    N ⟶ ModuleCat.of R (S.X₁ × S.X₃) :=
  ModuleCat.ofHom (LinearMap.prod (s.r.hom.comp dL.hom) dM.hom)

/-- The split-product lift followed by the product-to-middle isomorphism recovers the middle
differential in a commuting square. -/
theorem exteriorComparisonProductLift_comp (s : S.Splitting)
    (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃) (hcomm : dL ≫ S.g = dM) :
    exteriorComparisonProductLift s dL dM ≫ s.prodIso.hom = dL := by
  have hfst : s.prodIso.inv ≫ ModuleCat.ofHom (LinearMap.fst R S.X₁ S.X₃) = s.r := by
    change biprod.lift s.r S.g ≫ (ModuleCat.biprodIsoProd S.X₁ S.X₃).hom ≫
      ModuleCat.ofHom (LinearMap.fst R S.X₁ S.X₃) = s.r
    have hf : (ModuleCat.biprodIsoProd S.X₁ S.X₃).hom ≫
        ModuleCat.ofHom (LinearMap.fst R S.X₁ S.X₃) = biprod.fst := by
      rw [← cancel_epi (ModuleCat.biprodIsoProd S.X₁ S.X₃).inv]
      simp
    rw [hf, biprod.lift_fst]
  have hsnd : s.prodIso.inv ≫ ModuleCat.ofHom (LinearMap.snd R S.X₁ S.X₃) = S.g := by
    change biprod.lift s.r S.g ≫ (ModuleCat.biprodIsoProd S.X₁ S.X₃).hom ≫
      ModuleCat.ofHom (LinearMap.snd R S.X₁ S.X₃) = S.g
    have hf : (ModuleCat.biprodIsoProd S.X₁ S.X₃).hom ≫
        ModuleCat.ofHom (LinearMap.snd R S.X₁ S.X₃) = biprod.snd := by
      rw [← cancel_epi (ModuleCat.biprodIsoProd S.X₁ S.X₃).inv]
      simp
    rw [hf, biprod.lift_snd]
  apply (cancel_mono s.prodIso.inv).1
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ((ModuleCat.Hom.hom (exteriorComparisonProductLift s dL dM)) x : S.X₁ × S.X₃) =
    (ModuleCat.Hom.hom (dL ≫ s.prodIso.inv) x : S.X₁ × S.X₃)
  apply Prod.ext
  · have hcomp : exteriorComparisonProductLift s dL dM ≫
        ModuleCat.ofHom (LinearMap.fst R S.X₁ S.X₃) =
        dL ≫ s.prodIso.inv ≫ ModuleCat.ofHom (LinearMap.fst R S.X₁ S.X₃) := by
      rw [← Category.assoc, Category.assoc, hfst]
      rfl
    exact ConcreteCategory.congr_hom hcomp x
  · have hcomp : exteriorComparisonProductLift s dL dM ≫
        ModuleCat.ofHom (LinearMap.snd R S.X₁ S.X₃) =
        dL ≫ s.prodIso.inv ≫ ModuleCat.ofHom (LinearMap.snd R S.X₁ S.X₃) := by
      rw [← Category.assoc, Category.assoc, hsnd, hcomm]
      rfl
    exact ConcreteCategory.congr_hom hcomp x

/-- The exterior comparison before passage to the cokernel, constructed in a product model of
the split short exact row. -/
noncomputable def exteriorComparisonPre (s : S.Splitting)
    (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ) :
    S.X₂.exteriorPower p →ₗ[R]
      S.X₁.exteriorPower p ⊗[R] (det[R](N) →ₗ[R] det[R](S.X₃)) :=
  let n := Module.finrank R N
  let product := ModuleCat.of R (S.X₁ × S.X₃)
  let wedgeMap : S.X₂.exteriorPower p ⊗[R] N.exteriorPower n →ₗ[R]
      S.X₁.exteriorPower p ⊗[R] S.X₃.exteriorPower n :=
    (ModuleCat.exteriorPower.bidegreeProjection (Iso.refl product) p n).comp
      ((ModuleCat.exteriorPower.mul product p n).hom.comp
        (TensorProduct.map
          (ModuleCat.exteriorPower.map s.prodIso.inv p).hom
          (ModuleCat.exteriorPower.map
            (exteriorComparisonProductLift s dL dM) n).hom))
  (TensorProduct.map LinearMap.id
      (ModuleCat.Determinant.mapTopExteriorPower N S.X₃ n rfl hRank.symm)).comp
    ((lTensorHomEquivHomLTensor R (⋀[R]^n N)
      (S.X₁.exteriorPower p) (S.X₃.exteriorPower n)).symm.toLinearMap.comp
        (TensorProduct.lcurry (RingHom.id R) _ _ _ wedgeMap))

/-- The precomparison map does not depend on the splitting of the short exact row. -/
theorem exteriorComparisonPre_independent (s t : S.Splitting)
    (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃) (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ) :
    exteriorComparisonPre s dL dM hRank p =
      exteriorComparisonPre t dL dM hRank p := sorry

/-- The precomparison kills the kernel of the exterior-power map to the cokernel of the middle
differential. -/
theorem exteriorComparisonPre_ker (s : S.Splitting)
    (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃) (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ) :
    LinearMap.ker (ModuleCat.exteriorPower.map (cokernel.π dL) p).hom ≤
      LinearMap.ker (exteriorComparisonPre s dL dM hRank p) := sorry

/-- The exterior-power map induced by a cokernel projection is surjective. -/
theorem cokernelExteriorPower_surjective (dL : N ⟶ S.X₂) (p : ℕ) :
    Function.Surjective (ModuleCat.exteriorPower.map (cokernel.π dL) p) := by
  exact _root_.exteriorPower.map_surjective
    ((ModuleCat.epi_iff_surjective (cokernel.π dL)).mp inferInstance)

/-- The canonical family of comparison maps attached to a short exact row and a commuting
two-term differential from `N` to its middle and right terms. -/
noncomputable def exteriorComparison
    (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃)
    (p : ℕ) : (cokernel dL).exteriorPower p →ₗ[R]
      S.X₁.exteriorPower p ⊗[R] (det[R](N) →ₗ[R] det[R](S.X₃)) :=
  let s := hS.splittingOfProjective
  let f : S.X₂.exteriorPower p →ₗ[R] ModuleCat.of R
      (S.X₁.exteriorPower p ⊗[R] (det[R](N) →ₗ[R] det[R](S.X₃))) :=
    exteriorComparisonPre s dL dM hRank p
  ModuleCat.exteriorPower.descOfSurjective (cokernel.π dL) p
    (cokernelExteriorPower_surjective dL p)
    f
    (exteriorComparisonPre_ker s dL dM hcomm hRank p)

/-- The canonical comparison recovers its precomparison after the exterior-power cokernel map. -/
theorem exteriorComparison_comp_map
    (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ) :
    (exteriorComparison hS dL dM hcomm hRank p).comp
        (ModuleCat.exteriorPower.map (cokernel.π dL) p).hom =
      exteriorComparisonPre hS.splittingOfProjective dL dM hRank p := by
  apply LinearMap.ext
  intro x
  dsimp [exteriorComparison, ModuleCat.exteriorPower.descOfSurjective]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

/-- The canonical exterior comparison is uniquely determined by its precomparison composite. -/
theorem exteriorComparison_unique
    (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃) (p : ℕ)
    (c : (cokernel dL).exteriorPower p →ₗ[R]
      S.X₁.exteriorPower p ⊗[R] (det[R](N) →ₗ[R] det[R](S.X₃)))
    (hc : c.comp (ModuleCat.exteriorPower.map (cokernel.π dL) p).hom =
      exteriorComparisonPre hS.splittingOfProjective dL dM hRank p) :
    c = exteriorComparison hS dL dM hcomm hRank p := by
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := cokernelExteriorPower_surjective dL p y
  exact (LinearMap.congr_fun hc x).trans
    (LinearMap.congr_fun (exteriorComparison_comp_map hS dL dM hcomm hRank p) x).symm

/-- In degree zero, the exterior comparison carries the exterior unit to the discriminant of
the two-term complex `N ⟶ S.X₃`. -/
theorem exteriorComparison_zero
    (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃) :
    exteriorComparison hS dL dM hcomm hRank 0
        (ModuleCat.exteriorPower.oneLinear (cokernel dL) (1 : R)) =
      ModuleCat.exteriorPower.oneLinear S.X₁ (1 : R) ⊗ₜ[R]
        ModuleCat.twoTermDiscriminant dM hRank := sorry

/-- The exterior comparisons commute with left exterior multiplication by classes from
`S.X₁`. -/
theorem exteriorComparison_wedge
    (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃)
    (q p : ℕ) (ω : S.X₁.exteriorPower q) (η : (cokernel dL).exteriorPower p) :
    exteriorComparison hS dL dM hcomm hRank (q + p)
        (ModuleCat.exteriorPower.mul (cokernel dL) q p
          (ModuleCat.exteriorPower.map (S.f ≫ cokernel.π dL) q ω ⊗ₜ[R] η)) =
      TensorProduct.map (ModuleCat.exteriorPower.mul S.X₁ q p).hom LinearMap.id
        ((TensorProduct.assoc R (S.X₁.exteriorPower q) (S.X₁.exteriorPower p)
          (det[R](N) →ₗ[R] det[R](S.X₃))).symm
            (ω ⊗ₜ[R] exteriorComparison hS dL dM hcomm hRank p η)) := sorry

private theorem exteriorPower_mul_oneLinear (M : ModuleCat.{v} R) (p : ℕ) (x : M.exteriorPower p) :
    ModuleCat.exteriorPower.mul M p 0
      (x ⊗ₜ[R] ModuleCat.exteriorPower.oneLinear M (1 : R)) = x := by
  apply Subtype.ext
  change ((⋀[R]^p M).subtype x) *
    ((⋀[R]^0 M).subtype ((exteriorPower.zeroEquiv R M).symm 1)) =
      (⋀[R]^p M).subtype x
  simp [exteriorPower.zeroEquiv_symm_apply]

/-- Composing the exterior comparison with the map from `S.X₁` is tensor multiplication by
the discriminant of `N ⟶ S.X₃`. -/
theorem exteriorComparison_comp
    (hS : S.ShortExact) (dL : N ⟶ S.X₂) (dM : N ⟶ S.X₃)
    (hcomm : dL ≫ S.g = dM)
    [Module.Free R N] [Module.Finite R N]
    [Module.Free R S.X₃] [Module.Finite R S.X₃]
    (hRank : Module.finrank R N = Module.finrank R S.X₃)
    (p : ℕ) :
    (exteriorComparison hS dL dM hcomm hRank p).comp
        (ModuleCat.exteriorPower.map (S.f ≫ cokernel.π dL) p).hom =
      (TensorProduct.mk R (S.X₁.exteriorPower p)
        (det[R](N) →ₗ[R] det[R](S.X₃))).flip
          (ModuleCat.twoTermDiscriminant dM hRank) := by
  apply LinearMap.ext
  intro ω
  have hw := exteriorComparison_wedge hS dL dM hcomm hRank p 0 ω
    (ModuleCat.exteriorPower.oneLinear (cokernel dL) (1 : R))
  rw [exteriorComparison_zero hS dL dM hcomm hRank] at hw
  have hleft := exteriorPower_mul_oneLinear (cokernel dL) p
    ((ModuleCat.exteriorPower.map (S.f ≫ cokernel.π dL) p).hom ω)
  have hright := exteriorPower_mul_oneLinear S.X₁ p ω
  change exteriorComparison hS dL dM hcomm hRank p
      ((ModuleCat.exteriorPower.map (S.f ≫ cokernel.π dL) p).hom ω) =
    ω ⊗ₜ[R] ModuleCat.twoTermDiscriminant dM hRank
  have htarget : TensorProduct.map (ModuleCat.exteriorPower.mul S.X₁ p 0).hom LinearMap.id
      ((TensorProduct.assoc R (S.X₁.exteriorPower p) (S.X₁.exteriorPower 0)
        (det[R](N) →ₗ[R] det[R](S.X₃))).symm
        (ω ⊗ₜ[R] (ModuleCat.exteriorPower.oneLinear S.X₁ 1 ⊗ₜ[R]
          ModuleCat.twoTermDiscriminant dM hRank))) =
      ω ⊗ₜ[R] ModuleCat.twoTermDiscriminant dM hRank := by
    simp only [TensorProduct.assoc_symm_tmul, TensorProduct.map_tmul, LinearMap.id_apply]
    exact congrArg (fun x : S.X₁.exteriorPower p ↦
      x ⊗ₜ[R] ModuleCat.twoTermDiscriminant dM hRank) hright
  exact (congrArg (exteriorComparison hS dL dM hcomm hRank p) hleft.symm).trans
    (hw.trans htarget)

end CategoryTheory.ShortComplex.ShortExact

end
