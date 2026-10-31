/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Extension.Cotangent.Naturality
public import ReasLib.RingTheory.Extension.Cotangent.PresentationSequence
public import ReasLib.RingTheory.Ideal.Regularity.Quotient
import Mathlib.Tactic.CrossRefAttribute

/-!
# Presentation-level Jacobi-Zariski sequences

This leaf owns the canonical map from the tensorized naive cotangent complex of a
presentation to cotangent homology. It also packages the conormal and left
Jacobi-Zariski rows as short complexes.

@stack 07D4
-/

@[expose] public section

open Algebra CategoryTheory
open scoped TensorProduct

universe u v w

noncomputable section

variable {A B C : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable {ι : Type v} {κ : Type w}

private theorem cotangent_liftBaseChange_eq_on_cycles
    (P : Generators A B ι) (W : Extension.{w} A C)
    (f g : P.toExtension.Hom W)
    (x : C ⊗[B] P.toExtension.Cotangent)
    (hx : x ∈ LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex)) :
    (Extension.Cotangent.map f).liftBaseChange C x =
      (Extension.Cotangent.map g).liftBaseChange C x := by
  have h : (Extension.Cotangent.map f).liftBaseChange C -
      (Extension.Cotangent.map g).liftBaseChange C =
      (f.sub g).liftBaseChange C ∘ₗ P.toExtension.cotangentComplex.baseChange C := by
    apply LinearMap.ext
    intro z
    induction z with
    | zero => simp only [map_zero]
    | tmul r y =>
      simp only [LinearMap.sub_apply, LinearMap.liftBaseChange_tmul, LinearMap.comp_apply,
        LinearMap.baseChange_tmul]
      rw [← smul_sub, ← LinearMap.sub_apply, Extension.Cotangent.map_sub_map]
      rfl
    | add z z' hz hz' => simp only [map_add, hz, hz']
  have hx' := DFunLike.congr_fun h x
  change P.toExtension.cotangentComplex.baseChange C x = 0 at hx
  apply sub_eq_zero.mp
  simpa only [LinearMap.sub_apply, LinearMap.comp_apply, hx, map_zero] using hx'

private theorem equivH1Cotangent_map_naturality
    (W : Generators A C ι) (Q : Generators B C κ) (f : W.Hom Q) :
    Q.equivH1Cotangent.toLinearMap ∘ₗ Extension.H1Cotangent.map f.toExtensionHom =
      H1Cotangent.map A B C C ∘ₗ W.equivH1Cotangent.toLinearMap := by
  apply LinearMap.ext
  intro x
  change Extension.H1Cotangent.map (Generators.defaultHom Q (Generators.self B C)).toExtensionHom
      (Extension.H1Cotangent.map f.toExtensionHom x) =
    Extension.H1Cotangent.map
      (Generators.defaultHom (Generators.self A C) (Generators.self B C)).toExtensionHom
      (Extension.H1Cotangent.map
        (Generators.defaultHom W (Generators.self A C)).toExtensionHom x)
  rw [← Extension.H1Cotangent.map_comp_apply, ← Extension.H1Cotangent.map_comp_apply,
    Extension.H1Cotangent.map_eq]

/-- The tensorized conormal map associated to `Q.toComp P` sends cycles to cycles. -/
theorem tensor_presentation_conormal_map_mem_comp_generators_h1
    (P : Generators A B ι) (Q : Generators B C κ)
    (x : C ⊗[B] P.toExtension.Cotangent)
    (hx : x ∈ LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex)) :
    LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x ∈
      LinearMap.ker (Q.comp P).toExtension.cotangentComplex := by
  rw [LinearMap.mem_ker] at hx ⊢
  change ((Q.comp P).toExtension.cotangentComplex ∘ₗ
    LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom)) x = 0
  rw [← Generators.H1Cotangent.map_comp_cotangentComplex_baseChange Q P]
  simp [hx]

/-- The canonical map from tensorized presentation cycles for `P` to the first cotangent
homology of the composite presentation `Q.comp P`. -/
@[stacks 07D4 "tensorized presentation cotangent map"]
noncomputable def tensor_presentation_cotangent_h1_to_comp_generators_h1
    (P : Generators A B ι) (Q : Generators B C κ) :
    LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
      (Q.comp P).toExtension.H1Cotangent :=
  (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom)).restrict
    (tensor_presentation_conormal_map_mem_comp_generators_h1 P Q)

/-- The canonical left Jacobi-Zariski map from tensorized presentation homology to
`H1Cotangent A C`. -/
@[stacks 07D4 "presentation-level left Jacobi-Zariski map"]
noncomputable def tensor_presentation_cotangent_h1_to_h1_cotangent
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
      H1Cotangent A C :=
  ((Generators.self B C).comp P).equivH1Cotangent.toLinearMap ∘ₗ
    tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C)

private theorem tensor_presentation_cotangent_h1_to_h1_cotangent_eq_comp
    (P : Generators A B ι) (Q : Generators B C κ) :
    tensor_presentation_cotangent_h1_to_h1_cotangent C P =
      (Q.comp P).equivH1Cotangent.toLinearMap ∘ₗ
        tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ((Extension.Cotangent.map (Generators.defaultHom
      ((Generators.self B C).comp P) (Generators.self A C)).toExtensionHom) ∘ₗ
      (Extension.Cotangent.map ((Generators.self B C).toComp P).toExtensionHom).liftBaseChange C) x.1 =
    ((Extension.Cotangent.map (Generators.defaultHom
      (Q.comp P) (Generators.self A C)).toExtensionHom) ∘ₗ
      (Extension.Cotangent.map (Q.toComp P).toExtensionHom).liftBaseChange C) x.1
  rw [LinearMap.liftBaseChange_comp, LinearMap.liftBaseChange_comp,
    ← Extension.Cotangent.map_comp, ← Extension.Cotangent.map_comp]
  exact cotangent_liftBaseChange_eq_on_cycles P (Generators.self A C).toExtension _ _ x.1 x.2

/-- The left map in the conormal row of the composite presentation `Q.comp P`, with universe
levels normalized by `ULift`. -/
@[stacks 07D4 "composite-presentation conormal left map"]
noncomputable def compPresentationConormalLeftMap
    (P : Generators A B ι) (Q : Generators B C κ) :
    ULift.{max u (max v w), max u v} (C ⊗[B] P.toExtension.Cotangent) →ₗ[C]
      ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent :=
  (ULift.moduleEquiv :
      ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent ≃ₗ[C]
        (Q.comp P).toExtension.Cotangent).symm.toLinearMap ∘ₗ
    LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) ∘ₗ
    (ULift.moduleEquiv :
      ULift.{max u (max v w), max u v} (C ⊗[B] P.toExtension.Cotangent) ≃ₗ[C]
        (C ⊗[B] P.toExtension.Cotangent)).toLinearMap

/-- The right map in the conormal row of the composite presentation `Q.comp P`, with universe
levels normalized by `ULift`. -/
@[stacks 07D4 "composite-presentation conormal right map"]
noncomputable def compPresentationConormalRightMap
    (P : Generators A B ι) (Q : Generators B C κ) :
    ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent →ₗ[C]
      ULift.{max u (max v w), max u w} Q.toExtension.Cotangent :=
  (ULift.moduleEquiv :
      ULift.{max u (max v w), max u w} Q.toExtension.Cotangent ≃ₗ[C]
        Q.toExtension.Cotangent).symm.toLinearMap ∘ₗ
    Extension.Cotangent.map (Q.ofComp P).toExtensionHom ∘ₗ
    (ULift.moduleEquiv :
      ULift.{max u (max v w), max u (max v w)} (Q.comp P).toExtension.Cotangent ≃ₗ[C]
        (Q.comp P).toExtension.Cotangent).toLinearMap

/-- The two maps in the composite-presentation conormal row compose to zero. -/
theorem compPresentationConormalSequence_comp_eq_zero
    (P : Generators A B ι) (Q : Generators B C κ) :
    (compPresentationConormalRightMap P Q).comp (compPresentationConormalLeftMap P Q) = 0 := by
  apply LinearMap.ext
  intro x
  apply (ULift.moduleEquiv :
    ULift.{max u (max v w), max u w} Q.toExtension.Cotangent ≃ₗ[C]
      Q.toExtension.Cotangent).injective
  simpa [compPresentationConormalLeftMap, compPresentationConormalRightMap] using
    DFunLike.congr_fun (Generators.Cotangent.exact Q P).linearMap_comp_eq_zero x.down

/-- The conormal short complex
`C ⊗[B] I / I^2 ⟶ K / K^2 ⟶ J / J^2` of a composite presentation. -/
@[stacks 07D4 "composite-presentation conormal sequence"]
noncomputable def compPresentationConormalSequence
    (P : Generators A B ι) (Q : Generators B C κ) :
    ShortComplex (ModuleCat.{max u (max v w)} C) :=
  ModuleCat.shortComplexOfCompEqZero
    (compPresentationConormalLeftMap P Q)
    (compPresentationConormalRightMap P Q)
    (compPresentationConormalSequence_comp_eq_zero P Q)

/-- The left map in the presentation-level Jacobi-Zariski row. -/
@[stacks 07D4 "presentation-level Jacobi-Zariski left map"]
noncomputable def presentationJacobiZariskiLeftMap
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) →ₗ[C]
      ULift.{max u v, u} (H1Cotangent A C) :=
  (ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C]
      H1Cotangent A C).symm.toLinearMap ∘ₗ
    tensor_presentation_cotangent_h1_to_h1_cotangent C P

/-- The left two maps in the presentation-level Jacobi-Zariski row compose to zero. -/
theorem presentationJacobiZariskiLeftSequence_comp_eq_zero
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    ((ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent B C) ≃ₗ[C]
          H1Cotangent B C).symm.toLinearMap ∘ₗ
        H1Cotangent.map A B C C ∘ₗ
        (ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C]
          H1Cotangent A C).toLinearMap).comp
      (presentationJacobiZariskiLeftMap C P) = 0 := by
  apply LinearMap.ext
  intro x
  apply (ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent B C) ≃ₗ[C]
    H1Cotangent B C).injective
  change (H1Cotangent.map A B C C ∘ₗ
    ((Generators.self B C).comp P).equivH1Cotangent.toLinearMap)
      (tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C) x) = 0
  rw [← equivH1Cotangent_map_naturality _ _ ((Generators.self B C).ofComp P)]
  change (Generators.self B C).equivH1Cotangent
    (Extension.H1Cotangent.map ((Generators.self B C).ofComp P).toExtensionHom
      (tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C) x)) = 0
  have hz : Extension.H1Cotangent.map ((Generators.self B C).ofComp P).toExtensionHom
      (tensor_presentation_cotangent_h1_to_comp_generators_h1 P (Generators.self B C) x) = 0 := by
    apply Subtype.ext
    exact DFunLike.congr_fun
      (Generators.Cotangent.exact (Generators.self B C) P).linearMap_comp_eq_zero x.1
  rw [hz, map_zero]

/-- The left three-term Jacobi-Zariski short complex
`H1(NL(B / A) ⊗[B] C) ⟶ H1Cotangent A C ⟶ H1Cotangent B C`. -/
@[stacks 07D4 "presentation-level left Jacobi-Zariski sequence"]
noncomputable def presentationJacobiZariskiLeftSequence
    (C : Type u) [CommRing C] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    (P : Generators A B ι) :
    ShortComplex (ModuleCat.{max u v} C) :=
  ModuleCat.shortComplexOfCompEqZero
    (R := C)
    (M := LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex))
    (N := ULift.{max u v, u} (H1Cotangent A C))
    (L := ULift.{max u v, u} (H1Cotangent B C))
    (presentationJacobiZariskiLeftMap C P)
    ((ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent B C) ≃ₗ[C]
        H1Cotangent B C).symm.toLinearMap ∘ₗ
      H1Cotangent.map A B C C ∘ₗ
      (ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C]
        H1Cotangent A C).toLinearMap)
    (presentationJacobiZariskiLeftSequence_comp_eq_zero C P)

/-- Lemma 15.33.6 (1), tag `07D4`: a finite
Koszul-regular presentation of `C` over `B` makes the composite-presentation conormal row short
exact. -/
@[stacks 07D4 "(1)"]
theorem comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel
    [Finite κ] (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal Q.toExtension.ker) :
    (compPresentationConormalSequence P Q).ShortExact := sorry

/-- Exactness on presentation cycles follows from short exactness of the conormal row. -/
theorem tensor_presentation_cotangent_h1_to_comp_generators_h1_exact_of_conormal_shortExact
    (P : Generators A B ι) (Q : Generators B C κ)
    (hShort : (compPresentationConormalSequence P Q).ShortExact) :
    Function.Exact
      (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q)
      (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom) := by
  apply LinearMap.exact_of_comp_of_mem_range
  · apply LinearMap.ext
    intro x
    apply Subtype.ext
    change Extension.Cotangent.map (Q.ofComp P).toExtensionHom
      (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x.1) = 0
    exact DFunLike.congr_fun (Generators.Cotangent.exact Q P).linearMap_comp_eq_zero x.1
  · intro x hx
    have hx' : x.1 ∈ LinearMap.ker (Extension.Cotangent.map (Q.ofComp P).toExtensionHom) := by
      exact congrArg Subtype.val hx
    rw [(Generators.Cotangent.exact Q P).linearMap_ker_eq] at hx'
    obtain ⟨y, hy⟩ := hx'
    have hy' : y ∈ LinearMap.ker (LinearMap.baseChange C P.toExtension.cotangentComplex) := by
      rw [LinearMap.mem_ker]
      apply Generators.CotangentSpace.map_toComp_injective Q P
      rw [map_zero]
      change ((Extension.CotangentSpace.map (Q.toComp P).toExtensionHom).liftBaseChange C ∘ₗ
        LinearMap.baseChange C P.toExtension.cotangentComplex) y = 0
      rw [Generators.H1Cotangent.map_comp_cotangentComplex_baseChange Q P]
      change (Q.comp P).toExtension.cotangentComplex
        (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) y) = 0
      rw [hy]
      exact x.2
    exact ⟨⟨y, hy'⟩, Subtype.ext hy⟩

/-- Exactness computed with a chosen composite presentation transports to canonical cotangent
homology. -/
theorem tensor_presentation_cotangent_h1_to_h1_cotangent_exact_of_comp_exact
    (P : Generators A B ι) (Q : Generators B C κ)
    (hExact : Function.Exact
      (tensor_presentation_cotangent_h1_to_comp_generators_h1 P Q)
      (Extension.H1Cotangent.map (Q.ofComp P).toExtensionHom)) :
    Function.Exact
      (tensor_presentation_cotangent_h1_to_h1_cotangent C P)
      (H1Cotangent.map A B C C) := by
  refine Function.Exact.of_ladder_linearEquiv_of_exact
    (e₁ := LinearEquiv.refl C _)
    (e₂ := (Q.comp P).equivH1Cotangent) (e₃ := Q.equivH1Cotangent) ?_ ?_ hExact
  · simpa using tensor_presentation_cotangent_h1_to_h1_cotangent_eq_comp P Q
  · exact (equivH1Cotangent_map_naturality _ _ (Q.ofComp P)).symm

/-- The Koszul-regular presentation criterion simultaneously gives injectivity of the left
Jacobi-Zariski map and exactness at its middle term. -/
theorem jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel
    [Finite κ] (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal Q.toExtension.ker) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) ∧
      (presentationJacobiZariskiLeftSequence C P).Exact := by
  have hShort := comp_presentation_conormal_sequence_exact_of_koszul_regular_kernel P Q hQ
  constructor
  · rw [tensor_presentation_cotangent_h1_to_h1_cotangent_eq_comp P Q]
    apply (Q.comp P).equivH1Cotangent.injective.comp
    intro x y h
    apply Subtype.ext
    have h' : compPresentationConormalLeftMap P Q (ULift.up x.1) =
        compPresentationConormalLeftMap P Q (ULift.up y.1) := by
      change ULift.up
        (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) x.1) =
        ULift.up
        (LinearMap.liftBaseChange C (Extension.Cotangent.map (Q.toComp P).toExtensionHom) y.1)
      exact congrArg ULift.up (congrArg Subtype.val h)
    exact congrArg ULift.down (hShort.moduleCat_injective_f h')
  · have hExact := tensor_presentation_cotangent_h1_to_h1_cotangent_exact_of_comp_exact P Q
      (tensor_presentation_cotangent_h1_to_comp_generators_h1_exact_of_conormal_shortExact P Q hShort)
    apply ModuleCat.shortComplex_exact
    change Function.Exact
      ((ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C]
        H1Cotangent A C).symm.toLinearMap ∘ₗ
        tensor_presentation_cotangent_h1_to_h1_cotangent C P)
      ((ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent B C) ≃ₗ[C]
        H1Cotangent B C).symm.toLinearMap ∘ₗ
        (H1Cotangent.map A B C C ∘ₗ
          (ULift.moduleEquiv : ULift.{max u v, u} (H1Cotangent A C) ≃ₗ[C]
            H1Cotangent A C).toLinearMap))
    rw [LinearEquiv.postcomp_exact_iff_exact, LinearEquiv.conj_symm_exact_iff_exact]
    exact hExact

/-- Lemma 15.33.6 (2), tag `07D4`: the left map in the
presentation-level Jacobi-Zariski sequence is injective. -/
@[stacks 07D4 "(2)"]
theorem presentationJacobiZariskiLeftSequence_injective_f_of_koszul_regular_kernel
    [Finite κ] (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal Q.toExtension.ker) :
    Function.Injective (tensor_presentation_cotangent_h1_to_h1_cotangent C P) := by
  exact (jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel P Q hQ).1

/-- Lemma 15.33.6 (3), tag `07D4`: the left
presentation-level Jacobi-Zariski short complex is exact. -/
@[stacks 07D4 "(3)"]
theorem presentationJacobiZariskiLeftSequence_exact_of_koszul_regular_kernel
    [Finite κ] (P : Generators A B ι) (Q : Generators B C κ)
    (hQ : Ideal.IsKoszulRegularIdeal Q.toExtension.ker) :
    (presentationJacobiZariskiLeftSequence C P).Exact := by
  exact (jacobi_zariski_sequence_exact_with_zero_left_of_koszul_regular_kernel P Q hQ).2
