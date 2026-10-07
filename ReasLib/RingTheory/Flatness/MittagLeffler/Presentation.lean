module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.LinearAlgebra.TensorProduct.Domination
public import ReasLib.RingTheory.Flatness.MittagLeffler.KernelFactorization.ULift
public import ReasLib.RingTheory.Flatness.MittagLeffler.TailFactorization
import ReasLib.LinearAlgebra.TensorProduct.Domination.FinitePresentation
import ReasLib.LinearAlgebra.TensorProduct.Domination.Pushout
import Mathlib.CategoryTheory.Presentable.Directed

@[expose] public section

/-!
# Mittag-Leffler Directed Presentations

This file separates the intrinsic tensor-kernel condition on a module from the four conditions
on a directed presentation and records their reusable pairwise comparison API.
-/

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v w x

noncomputable section

namespace Module.MittagLeffler

variable {R : Type u} [CommRing R]

namespace Presentation

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/-- The transition maps of a directed presentation eventually tensor-kernel dominate its
structure maps to the presented module. -/
@[stacks 059E "stage domination"]
abbrev StageDomination
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M)) : Prop :=
  ∀ i : I, ∃ (j : I) (hij : i ≤ j),
    LinearMap.Dominates.{u, max u v, max u v, max u v}
      (P.diag.map (homOfLE hij)).hom (P.ι.app i).hom

set_option maxHeartbeats 600000 in
private theorem exists_later_stage_rTensor_eq_zero
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    {i : I} (Q : Type (max u v)) [AddCommMonoid Q] [Module R Q]
    (z : P.diag.obj i ⊗[R] Q)
    (hz : ((P.ι.app i).hom.rTensor Q) z = 0) :
    ∃ (j : I) (hij : i ≤ j),
      (((P.diag.map (homOfLE hij)).hom.rTensor Q) z = 0) := by
  let addQ : AddCommMonoid Q := inferInstance
  letI : AddCommGroup Q := Module.addCommMonoidToAddCommGroup R
  letI : AddCommMonoid Q := addQ
  obtain ⟨j, e, he⟩ :=
    LinearMap.exists_later_stage_rTensor_eq_zero.{u, v}
      (R := R) (J := I) (L := Q) (Q := M) (P := P) (j := i) (a := z) hz
  let hij : i ≤ j := leOfHom e
  exact ⟨j, hij, by simpa only [Subsingleton.elim e (homOfLE hij)] using he⟩

/-- Finite kernel factorization is equivalent to eventual stage domination for a finitely
presented directed colimit presentation. -/
theorem kernelFactorization_iff_stageDomination
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    FiniteKernelFactorization R M ↔ StageDomination P := by
  constructor
  · intro hkernel i
    letI : Module.FinitePresentation R (P.diag.obj i) := hfp i
    obtain ⟨Q, g, hQ, hg_structure, hstructure_g⟩ :=
      hkernel (P.diag.obj i) (hfp i) (P.ι.app i).hom
    letI : Module.FinitePresentation R Q := hQ
    letI : Module.FinitePresentation R (Q ⧸ LinearMap.range g) :=
      Module.finitePresentation_of_surjective (LinearMap.range g).mkQ
        (Submodule.mkQ_surjective _) (by
          simpa only [Submodule.ker_mkQ] using Submodule.fg_range g)
    obtain ⟨h, hfac⟩ :=
      (LinearMap.Dominates.iff_factorsThrough g (P.ι.app i).hom).mp hstructure_g
    obtain ⟨k, q, hq⟩ :=
      ModuleCat.finitePresentation_exists_factor R P.isColimit (ModuleCat.ofHom h)
    obtain ⟨j, hij, hkj⟩ := exists_ge_ge i k
    let candidate : P.diag.obj i ⟶ P.diag.obj j :=
      ModuleCat.ofHom g ≫ q ≫ P.diag.map (homOfLE hkj)
    have hcandidate : candidate ≫ P.ι.app j = P.ι.app i := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (P.ι.app j).hom
        ((P.diag.map (homOfLE hkj)).hom (q (g x))) = (P.ι.app i).hom x
      calc
        _ = (P.ι.app k).hom (q (g x)) :=
          ConcreteCategory.congr_hom (P.w (homOfLE hkj)) (q (g x))
        _ = h (g x) := ConcreteCategory.congr_hom hq (g x)
        _ = (P.ι.app i).hom x := (LinearMap.congr_fun hfac x).symm
    have heq :
        P.diag.map (homOfLE hij) ≫ P.ι.app j =
          candidate ≫ P.ι.app j := by
      rw [P.w, hcandidate]
    obtain ⟨l, a, ha⟩ := ModuleCat.finitePresentation_exists_eq R P.isColimit
      (P.diag.map (homOfLE hij)) candidate heq
    let hil : i ≤ l := le_trans hij (leOfHom a)
    let H : Q →ₗ[R] P.diag.obj l :=
      (q ≫ P.diag.map (homOfLE hkj) ≫ P.diag.map a).hom
    have hcanon :
        (P.diag.map (homOfLE hil)).hom = H.comp g := by
      apply LinearMap.ext
      intro x
      have hcanonical :
          (P.diag.map (homOfLE hil)).hom x =
            (P.diag.map a).hom ((P.diag.map (homOfLE hij)).hom x) := by
        have hcat :
            P.diag.map (homOfLE hil) =
              P.diag.map (homOfLE hij) ≫ P.diag.map a := by
          calc
            P.diag.map (homOfLE hil) = P.diag.map (homOfLE hij ≫ a) := by
              congr 1
            _ = P.diag.map (homOfLE hij) ≫ P.diag.map a := P.diag.map_comp _ _
        exact ConcreteCategory.congr_hom hcat x
      calc
        _ = (P.diag.map a).hom ((P.diag.map (homOfLE hij)).hom x) := hcanonical
        _ = (P.diag.map a).hom (candidate x) := ConcreteCategory.congr_hom ha x
        _ = H (g x) := by
          simp only [candidate, H, ModuleCat.comp_apply, ModuleCat.hom_ofHom]
        _ = (H.comp g) x := rfl
    refine ⟨l, hil, ?_⟩
    exact (LinearMap.dominates_of_factorization ⟨H, hcanon⟩).trans hg_structure
  · intro hstage P₀ hP₀ f
    letI : Module.FinitePresentation R P₀ := hP₀
    obtain ⟨i, g, hg⟩ :=
      ModuleCat.finitePresentation_exists_factor R P.isColimit (ModuleCat.ofHom f)
    obtain ⟨j, hij, hdom⟩ := hstage i
    let transition := (P.diag.map (homOfLE hij)).hom
    let g' := transition.comp g.hom
    have hgf : (P.ι.app i).hom.comp g.hom = f := by
      have hgf' := congrArg ModuleCat.Hom.hom hg
      change (P.ι.app i).hom.comp g.hom = f at hgf'
      exact hgf'
    refine ⟨P.diag.obj j, g', hfp j, ?_, ?_⟩
    · have h : g'.Dominates ((P.ι.app i).hom.comp g.hom) := hdom.comp
      rw [hgf] at h
      exact h
    · refine LinearMap.dominates_of_factorization ⟨(P.ι.app j).hom, ?_⟩
      apply LinearMap.ext
      intro x
      change f x = (P.ι.app j).hom (transition (g x))
      have hgx := ConcreteCategory.congr_hom hg x
      change (P.ι.app i).hom (g x) = f x at hgx
      have hwx := ConcreteCategory.congr_hom (P.w (homOfLE hij)) (g x)
      change (P.ι.app j).hom (transition (g x)) = (P.ι.app i).hom (g x) at hwx
      exact hgx.symm.trans hwx.symm

/-- Eventual stage domination is equivalent to eventual tail factorization for a finitely
presented directed colimit presentation. -/
theorem stageDomination_iff_tailFactorization
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    StageDomination P ↔ P.diag.HasTailFactorization := by
  rw [CategoryTheory.Functor.hasTailFactorization_iff_of_preorder]
  constructor
  · intro hstage i
    obtain ⟨j, hij, hdom⟩ := hstage i
    refine ⟨j, hij, fun k hik ↦ ?_⟩
    let tik := (P.diag.map (homOfLE hik)).hom
    let tij := (P.diag.map (homOfLE hij)).hom
    have hstructure : (P.ι.app i).hom.Dominates tik :=
      LinearMap.dominates_of_factorization ⟨(P.ι.app k).hom, by
        exact (congrArg ModuleCat.Hom.hom (P.w (homOfLE hik))).symm⟩
    have htij : tij.Dominates tik := hdom.trans hstructure
    letI : Module.FinitePresentation R (P.diag.obj i) := hfp i
    letI : Module.FinitePresentation R (P.diag.obj k) := hfp k
    letI : Module.FinitePresentation R (P.diag.obj k ⧸ LinearMap.range tik) :=
      Module.finitePresentation_of_surjective (LinearMap.range tik).mkQ
        (Submodule.mkQ_surjective _) (by
          simpa only [Submodule.ker_mkQ] using Submodule.fg_range tik)
    obtain ⟨h, hh⟩ := (LinearMap.Dominates.iff_factorsThrough tik tij).mp htij
    refine ⟨ModuleCat.ofHom h, ?_⟩
    apply ModuleCat.hom_ext
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_ofHom] using hh
  · intro htail i
    obtain ⟨j, hij, hfactor⟩ := htail i
    refine ⟨j, hij, ?_⟩
    intro (Q : Type (max u v)) hQadd hQmodule z hz
    rw [LinearMap.mem_ker] at hz ⊢
    have hzero : ∃ (k : I) (hik : i ≤ k),
        ((P.diag.map (homOfLE hik)).hom.rTensor Q) z = 0 :=
      exists_later_stage_rTensor_eq_zero (R := R) (I := I) (M := M)
        (P := P) (i := i) Q z hz
    obtain ⟨k, hik, hzk⟩ := hzero
    obtain ⟨h, hh⟩ := hfactor k hik
    have hh' :
        (P.diag.map (homOfLE hij)).hom =
          h.hom.comp (P.diag.map (homOfLE hik)).hom :=
      congrArg ModuleCat.Hom.hom hh
    rw [hh', LinearMap.rTensor_comp_apply, hzk, map_zero]

/-- Finite kernel factorization is equivalent to eventual tail factorization for a finitely
presented directed colimit presentation. -/
theorem kernelFactorization_iff_tailFactorization
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    FiniteKernelFactorization R M ↔ P.diag.HasTailFactorization :=
  (kernelFactorization_iff_stageDomination P hfp).trans
    (stageDomination_iff_tailFactorization P hfp)

/-- Finite kernel factorization is equivalent to all-target Hom Mittag-Lefflerness for a
finitely presented directed colimit presentation. -/
theorem kernelFactorization_iff_homMittagLeffler
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    FiniteKernelFactorization R M ↔ P.diag.HomMittagLeffler :=
  (kernelFactorization_iff_tailFactorization P hfp).trans
    (CategoryTheory.Functor.HomMittagLeffler.iff_tailFactorization P.diag).symm

/-- Finite kernel factorization is equivalent to the single product-target Hom test for a
finitely presented directed colimit presentation. -/
theorem kernelFactorization_iff_productHomMittagLeffler
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    FiniteKernelFactorization R M ↔
      ModuleCat.ProductHomMittagLeffler.{u, v, v, u} P.diag :=
  (kernelFactorization_iff_tailFactorization P hfp).trans
    (ModuleCat.ProductHomMittagLeffler.iff_tailFactorization P.diag).symm

/-- Eventual stage domination is equivalent to all-target Hom Mittag-Lefflerness for a finitely
presented directed colimit presentation. -/
theorem stageDomination_iff_homMittagLeffler
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    StageDomination P ↔ P.diag.HomMittagLeffler :=
  (stageDomination_iff_tailFactorization P hfp).trans
    (CategoryTheory.Functor.HomMittagLeffler.iff_tailFactorization P.diag).symm

/-- Eventual stage domination is equivalent to the single product-target Hom test for a finitely
presented directed colimit presentation. -/
theorem stageDomination_iff_productHomMittagLeffler
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    StageDomination P ↔
      ModuleCat.ProductHomMittagLeffler.{u, v, v, u} P.diag :=
  (stageDomination_iff_tailFactorization P hfp).trans
    (ModuleCat.ProductHomMittagLeffler.iff_tailFactorization P.diag).symm

/-- The five directed-presentation forms of the Mittag-Leffler condition. -/
@[stacks 059E]
theorem mittagLeffler_tfae
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    List.TFAE [
      FiniteKernelFactorization R M,
      StageDomination P,
      P.diag.HasTailFactorization,
      P.diag.HomMittagLeffler,
      ModuleCat.ProductHomMittagLeffler.{u, v, v, u} P.diag] := by
  tfae_have 1 ↔ 2 := kernelFactorization_iff_stageDomination P hfp
  tfae_have 2 ↔ 3 := stageDomination_iff_tailFactorization P hfp
  tfae_have 3 ↔ 4 :=
    (CategoryTheory.Functor.HomMittagLeffler.iff_tailFactorization P.diag).symm
  tfae_have 3 ↔ 5 :=
    (ModuleCat.ProductHomMittagLeffler.iff_tailFactorization P.diag).symm
  tfae_finish

end Presentation

section Intrinsic

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The presentation-based Mittag-Leffler property is equivalent to the intrinsic finite
tensor-kernel factorization condition. -/
@[stacks 059E "intrinsic criterion"]
theorem iff_finiteKernelFactorization :
    MittagLeffler R N ↔ FiniteKernelFactorization R N := by
  rw [← FiniteKernelFactorization.iff_ulift (R := R) (M := N)]
  constructor
  · rintro ⟨⟨P⟩⟩
    exact (Presentation.kernelFactorization_iff_homMittagLeffler
      P.toColimitPresentation P.isMittagLeffler.finitePresentation).2
        P.isMittagLeffler.homMittagLeffler
  · intro hkernel
    let X := ModuleCat.of.{max u w} R (ULift.{max u w} N)
    obtain ⟨J, _, _, P, hfp⟩ := ModuleCat.isFinitePresentation_ind (R := R) X
    obtain ⟨I, _, _, _, F, _⟩ := IsFiltered.exists_directed J
    let P' := P.reindex F
    have hfp' (i : I) : Module.FinitePresentation R (P'.diag.obj i) := hfp (F.obj i)
    have hhom : P'.diag.HomMittagLeffler :=
      (Presentation.kernelFactorization_iff_homMittagLeffler P' hfp').1 hkernel
    exact ⟨⟨Presentation.ofColimit P' ⟨hfp', hhom⟩⟩⟩

/-- A Mittag-Leffler module has finite tensor-kernel factorizations. -/
theorem finiteKernelFactorization (hN : MittagLeffler R N) :
    FiniteKernelFactorization R N := iff_finiteKernelFactorization.mp hN

/-- Finite tensor-kernel factorizations imply the Mittag-Leffler property. -/
theorem of_finiteKernelFactorization (hN : FiniteKernelFactorization R N) :
    MittagLeffler R N := iff_finiteKernelFactorization.mpr hN

end Intrinsic

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {M : Type (max u v)} [AddCommGroup M] [Module R M]

/-- For any finitely presented directed colimit presentation, the module is Mittag-Leffler
exactly when the presentation has eventual stage domination. -/
theorem Presentation.mittagLeffler_iff_stageDomination
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    MittagLeffler R M ↔ Presentation.StageDomination P :=
  iff_finiteKernelFactorization.trans
    (Presentation.kernelFactorization_iff_stageDomination P hfp)

/-- For any finitely presented directed colimit presentation, the module is Mittag-Leffler
exactly when all associated Hom inverse systems are Mittag-Leffler. -/
theorem Presentation.mittagLeffler_iff_homMittagLeffler
    (P : ColimitPresentation I (ModuleCat.of.{max u v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    MittagLeffler R M ↔ P.diag.HomMittagLeffler :=
  iff_finiteKernelFactorization.trans
    (Presentation.kernelFactorization_iff_homMittagLeffler P hfp)

end Module.MittagLeffler
