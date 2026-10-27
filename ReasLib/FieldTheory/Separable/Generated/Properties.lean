/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure
public import ReasLib.FieldTheory.Separable.Generated

@[expose] public section

/-!
# Properties of Separably Generated Extensions

This module contains reusable transport, restriction, and algebraic-specialization API for the
separably generated and separable-over predicates.  The definitions themselves live in
`ReasLib.FieldTheory.Separable.Generated` so clients that only need the predicates need not import
the stronger property API.
-/

universe u v w

open scoped IntermediateField

section

variable (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]

namespace Algebra

namespace IsSeparablyGenerated

variable {k' : Type u} {K' : Type v} [Field k'] [Field K'] [Algebra k' K']
variable {L : Type w} [Field L] [Algebra k' L]

/-- Separably generatedness is invariant under equivalence of field extensions over the base. -/
@[stacks 030O "equivalence transport"]
theorem of_algEquiv [IsSeparablyGenerated k' K'] (e : K' ≃ₐ[k'] L) :
    IsSeparablyGenerated k' L := by
  obtain ⟨s, hs, hsep⟩ := IsSeparablyGenerated.existsSeparatingBasis (k := k') (K := K')
  letI := hsep
  refine ⟨⟨e '' s, (isTranscendenceBasis_image e.injective.injOn).mp
    (e.isTranscendenceBasis hs), ?_⟩⟩
  let e' : IntermediateField.adjoin k' s ≃ₐ[k'] IntermediateField.adjoin k' (e '' s) :=
    (IntermediateField.intermediateFieldMap e _).trans
      (IntermediateField.equivOfEq (IntermediateField.adjoin_map k' s e.toAlgHom))
  exact Algebra.IsSeparable.of_equiv_equiv e'.toRingEquiv e.toRingEquiv (by
    ext x
    rfl)

/-- Explicit-hypothesis form of `of_algEquiv`; use this bridge when the source predicate is held
as a proposition value rather than an installed instance. -/
@[stacks 030O "explicit equivalence transport bridge"]
theorem of_algEquiv_of (hK : IsSeparablyGenerated k' K') (e : K' ≃ₐ[k'] L) :
    IsSeparablyGenerated k' L := by
  letI := hK
  exact of_algEquiv e

/-- For algebraic extensions, separably generatedness gives the usual separability predicate. -/
@[stacks 030X "algebraic specialization"]
theorem isSeparable [IsSeparablyGenerated k' K'] [Algebra.IsAlgebraic k' K'] :
    Algebra.IsSeparable k' K' := by
  obtain ⟨s, hs, hsep⟩ := IsSeparablyGenerated.existsSeparatingBasis (k := k') (K := K')
  haveI : IsEmpty s := hs.1.isEmpty_of_isAlgebraic
  have hs0 : s = ∅ := Set.isEmpty_coe_sort.mp inferInstance
  letI := hsep
  haveI : Algebra.IsSeparable (⊥ : IntermediateField k' K') K' :=
    Algebra.IsSeparable.of_equiv_equiv
      (IntermediateField.equivOfEq (show IntermediateField.adjoin k' s = ⊥ by
        rw [hs0, IntermediateField.adjoin_empty])).toRingEquiv
      (RingEquiv.refl K') (by
        ext x
        rfl)
  exact Algebra.isSeparable_tower_top_of_isSeparable (⊥ : IntermediateField k' K') k' K'

/-- Explicit-hypothesis form of `isSeparable`; use this bridge when separably generatedness is
available as a proposition rather than an installed instance. -/
@[stacks 030X "algebraic specialization bridge"]
theorem isSeparable_of
    (hK : IsSeparablyGenerated k' K') [Algebra.IsAlgebraic k' K'] :
    Algebra.IsSeparable k' K' := by
  letI := hK
  exact isSeparable

/-- Every separably generated field extension is separable over its base. -/
@[stacks 030X]
theorem isSeparableOver [IsSeparablyGenerated k' K'] :
    IsSeparableOver k' K' := sorry

/-- Explicit-hypothesis form of `isSeparableOver`; this keeps a proposition-valued witness from
being installed as a global instance merely to apply the canonical bridge. -/
@[stacks 030X "explicit hypothesis bridge"]
theorem isSeparableOver_of (hK : IsSeparablyGenerated k' K') :
    IsSeparableOver k' K' := by
  letI := hK
  exact isSeparableOver

end IsSeparablyGenerated

namespace IsSeparableOver

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]
variable {L : Type w} [Field L] [Algebra F L]

/-- Separability over the base is invariant under equivalence of field extensions over that base. -/
@[stacks 030P "equivalence transport"]
theorem of_algEquiv [IsSeparableOver F E] (e : E ≃ₐ[F] L) :
    IsSeparableOver F L := by
  constructor
  intro M hM
  have hmap : (M.map e.symm.toAlgHom).FG := by
    classical
    obtain ⟨s, rfl⟩ := hM
    exact ⟨s.image e.symm, by
      simpa only [Finset.coe_image, AlgEquiv.coe_toAlgHom] using
        (IntermediateField.adjoin_map F (s : Set L) e.symm.toAlgHom).symm⟩
  exact IsSeparablyGenerated.of_algEquiv_of
    (IsSeparableOver.isSeparablyGenerated_of_fg (M.map e.symm.toAlgHom) hmap)
    (M.equivMap e.symm.toAlgHom).symm

/-- Explicit-hypothesis form of `of_algEquiv`; use this bridge when separability over the base is
available as a proposition value rather than an installed instance. -/
@[stacks 030P "explicit equivalence transport bridge"]
theorem of_algEquiv_of (hK : IsSeparableOver F E) (e : E ≃ₐ[F] L) :
    IsSeparableOver F L := by
  letI := hK
  exact of_algEquiv e

/-- Restricting a separable-over extension to an intermediate field preserves separability over
the original base. -/
@[stacks 030P]
theorem of_intermediateField [IsSeparableOver F E] (L : IntermediateField F E) :
    IsSeparableOver F L := by
  constructor
  intro M hM
  have hmap : (M.map L.val).FG := by
    classical
    obtain ⟨s, rfl⟩ := hM
    exact ⟨s.image L.val, by
      simpa only [Finset.coe_image] using
        (IntermediateField.adjoin_map F (s : Set L) L.val).symm⟩
  exact IsSeparablyGenerated.of_algEquiv_of
    (IsSeparableOver.isSeparablyGenerated_of_fg (M.map L.val) hmap)
    (M.equivMap L.val).symm

/-- Explicit-hypothesis form of `of_intermediateField`; use this bridge when separability over the
base is available as a proposition value rather than an installed instance. -/
@[stacks 030P "explicit intermediate-field bridge"]
theorem of_intermediateField_of (hK : IsSeparableOver F E) (L : IntermediateField F E) :
    IsSeparableOver F L := by
  letI := hK
  exact of_intermediateField L

/-- Every extension of a perfect field is separable over that field. -/
@[stacks 030Y "perfect-field consequence"]
theorem of_perfectField [PerfectField F] : IsSeparableOver F E := by
  constructor
  intro K hK
  -- Local instance justification (proof-local temporary data): hK is converted to the EssFiniteType instance required only within this proof.
  letI : EssFiniteType F K := IntermediateField.essFiniteType_iff.mpr hK
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField F K
  have hs' : IsTranscendenceBasis F (fun x : (s : Set K) ↦ (x : K)) := by
    convert hs using 1 <;> simp only [Finset.coe_sort_coe]
  exact ⟨⟨(s : Set K), hs', hsep⟩⟩

/-- For algebraic extensions, separability over the base gives the usual separability predicate. -/
@[stacks 030X "algebraic specialization"]
theorem isSeparable [IsSeparableOver F E] [Algebra.IsAlgebraic F E] :
    Algebra.IsSeparable F E := by
  constructor
  intro x
  let M := F⟮x⟯
  haveI : IsSeparablyGenerated F M :=
    IsSeparableOver.isSeparablyGenerated_of_fg M
      (IntermediateField.fg_adjoin_of_finite (Set.finite_singleton x))
  haveI : Algebra.IsSeparable F M := IsSeparablyGenerated.isSeparable
  exact (Algebra.IsSeparable.isSeparable F (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : M)).map
    M.val M.val.injective

/-- Explicit-hypothesis form of `isSeparable`; use this bridge when separability over the base is
available as a proposition rather than an installed instance. -/
@[stacks 030X "algebraic specialization bridge"]
theorem isSeparable_of
    (hsep : IsSeparableOver F E) [Algebra.IsAlgebraic F E] :
    Algebra.IsSeparable F E := by
  letI := hsep
  exact isSeparable

/-- An essentially finite-type field extension that is separable over its base
is separably generated. -/
@[stacks 030X "essentially finite-type converse"]
theorem isSeparablyGenerated
    [IsSeparableOver F E] [EssFiniteType F E] :
    IsSeparablyGenerated F E :=
  IsSeparablyGenerated.of_algEquiv_of
    (IsSeparableOver.isSeparablyGenerated_of_fg (⊤ : IntermediateField F E)
      (IntermediateField.fg_top F E)) IntermediateField.topEquiv

end IsSeparableOver

namespace IsSeparablyGenerated

variable {F : Type u} {E : Type v} [Field F] [Field E] [Algebra F E]

/-- Explicit-hypothesis form of `Algebra.IsSeparableOver.isSeparablyGenerated`; this avoids
installing a separability proposition as a local instance merely to obtain the generatedness
conclusion. -/
@[stacks 030X "explicit essentially finite-type bridge"]
theorem of_isSeparableOver
    (hsep : IsSeparableOver F E) [EssFiniteType F E] :
    IsSeparablyGenerated F E := by
  letI := hsep
  exact IsSeparableOver.isSeparablyGenerated

end IsSeparablyGenerated

namespace IsSeparablyGenerated

/-- A separable algebraic field extension is separably generated. -/
@[stacks 030X "separable algebraic instance"]
instance instOfIsSeparable [Algebra.IsSeparable k K] :
    IsSeparablyGenerated k K := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k K
  haveI : IsEmpty s := hs.1.isEmpty_of_isAlgebraic
  have hs0 : s = ∅ := Set.isEmpty_coe_sort.mp inferInstance
  subst s
  refine ⟨⟨∅, hs, ?_⟩⟩
  exact Algebra.isSeparable_tower_top_of_isSeparable k (IntermediateField.adjoin k ∅) K

/-- A finitely generated extension of a perfect field is separably generated. -/
@[stacks 030Y "perfect-field finitely generated instance", instance low]
instance instOfPerfectField
    [PerfectField k] [EssFiniteType k K] : IsSeparablyGenerated k K := by
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K
  have hs' : IsTranscendenceBasis k (fun x : (s : Set K) ↦ (x : K)) := by
    convert hs using 1 <;> simp only [Finset.coe_sort_coe]
  exact ⟨⟨(s : Set K), hs', hsep⟩⟩

end IsSeparablyGenerated

namespace IsSeparableOver

/-- A separable algebraic field extension is separable over its base. -/
@[stacks 030X "separable algebraic instance"]
instance instOfIsSeparable [Algebra.IsSeparable k K] :
    IsSeparableOver k K := by
  constructor
  intro L _
  haveI : Algebra.IsSeparable k L :=
    Algebra.isSeparable_tower_bot_of_isSeparable k L K
  exact IsSeparablyGenerated.instOfIsSeparable k L

/-- A separably generated field extension is separable over its base.  The
low priority leaves a more specific algebraic-separability route preferred
when both are available. -/
@[stacks 030X "separably generated instance", instance low]
instance instOfSeparablyGenerated
    [IsSeparablyGenerated k K] : IsSeparableOver k K :=
  IsSeparablyGenerated.isSeparableOver

/-- Every extension of a perfect field is separable over its base. -/
@[stacks 030Y "perfect-field instance", instance low]
instance instOfPerfectField [PerfectField k] :
    IsSeparableOver k K := IsSeparableOver.of_perfectField

end IsSeparableOver

end Algebra

namespace PerfectField

/-- A field is perfect exactly when every field extension is separable over it. The
quantification ranges over a universe large enough to contain the base field, so the
characterization remains valid even when the extension universe is chosen below the base universe. -/
@[stacks 030Y]
theorem iff_forall_isSeparableOver {k : Type u} [Field k] :
    PerfectField k ↔
      ∀ (K : Type (max u v)) [Field K] [Algebra k K], Algebra.IsSeparableOver k K := by
  constructor
  · intro h K _ _
    letI := h
    exact Algebra.IsSeparableOver.of_perfectField
  · intro h
    haveI : Algebra.IsSeparableOver k (AlgebraicClosure k) :=
      Algebra.IsSeparableOver.of_algEquiv_of (h (ULift.{v} (AlgebraicClosure k)))
        ULift.algEquiv
    haveI : Algebra.IsSeparable k (AlgebraicClosure k) :=
      Algebra.IsSeparableOver.isSeparable
    exact (perfectField_iff_isSeparable_algebraicClosure k (AlgebraicClosure k)).mpr inferInstance

end PerfectField

end
