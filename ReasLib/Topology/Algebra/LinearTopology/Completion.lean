/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Completion of a linearly topologized module

The completion of a linearly topologized module is the inverse limit of the discrete
quotients `M ⧸ U` as `U` runs through open submodules.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped Topology

namespace IsLinearTopology

section induced

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsLinearTopology R M]

/-- The induced topology on a submodule of a linearly topologized module is linear. -/
instance instIsLinearTopology_subtype (N : Submodule R M) [IsLinearTopology R M] : IsLinearTopology R N where
  hasBasis_submodule' := sorry

/-- The quotient topology on a module by a submodule is linearly topologized when the
   quotient map is open. -/
instance instIsLinearTopology_quotient (N : Submodule R M) [ContinuousAdd M] [IsLinearTopology R M] :
    IsLinearTopology R (M ⧸ N) where
  hasBasis_submodule' := sorry

end induced

/-- The completion of a linearly topologized module, as the compatible families in its
   discrete quotients by open submodules. -/
def Completion (R : Type u) (M : Type v)
    [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsLinearTopology R M] :=
  { f : ∀ U : {U : Submodule R M // IsOpen (U : Set M)}, M ⧸ U.1 //
    ∀ (U U' : {U : Submodule R M // IsOpen (U : Set M)}) (h : U.1 ≤ U'.1),
      Submodule.factor h (f U) = f U' }

namespace Completion

variable {R : Type u} {M : Type v}
variable [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsLinearTopology R M]

/-- Zero is the compatible family of zero elements in all discrete quotients. -/
instance instZero : Zero (Completion R M) where
  zero := ⟨0, fun _ _ h ↦ map_zero (Submodule.factor h)⟩

/-- Addition of compatible families is defined pointwise in the discrete quotients. -/
instance instAdd : Add (Completion R M) where
  add x y :=
    ⟨x.1 + y.1, fun U U' h ↦
      (map_add (Submodule.factor h) (x.1 U) (y.1 U)).trans
        (congrArg₂ HAdd.hAdd (x.2 U U' h) (y.2 U U' h))⟩

/-- Negation of compatible families is defined pointwise in the discrete quotients. -/
instance instNeg : Neg (Completion R M) where
  neg x :=
    ⟨-x.1, fun U U' h ↦
      (map_neg (Submodule.factor h) (x.1 U)).trans (congrArg Neg.neg (x.2 U U' h))⟩

/-- Subtraction of compatible families is defined pointwise in the discrete quotients. -/
instance instSub : Sub (Completion R M) where
  sub x y :=
    ⟨x.1 - y.1, fun U U' h ↦
      (map_sub (Submodule.factor h) (x.1 U) (y.1 U)).trans
        (congrArg₂ HSub.hSub (x.2 U U' h) (y.2 U U' h))⟩

/-- Natural-number scalar multiplication of compatible families is pointwise. -/
instance instNSmul : SMul ℕ (Completion R M) where
  smul n x :=
    ⟨n • x.1, fun U U' h ↦
      (map_nsmul (Submodule.factor h) n (x.1 U)).trans (congrArg (n • ·) (x.2 U U' h))⟩

/-- Integer scalar multiplication of compatible families is pointwise. -/
instance instZSmul : SMul ℤ (Completion R M) where
  smul n x :=
    ⟨n • x.1, fun U U' h ↦
      (map_zsmul (Submodule.factor h) n (x.1 U)).trans (congrArg (n • ·) (x.2 U U' h))⟩

/-- Scalar multiplication by the base ring on compatible families is pointwise. -/
instance instSMul : SMul R (Completion R M) where
  smul r x :=
    ⟨r • x.1, fun U U' h ↦
      (map_smul (Submodule.factor h) r (x.1 U)).trans (congrArg (r • ·) (x.2 U U' h))⟩

/-- The completion is an abelian group under its pointwise operations. -/
instance instAddCommGroup : AddCommGroup (Completion R M) :=
  Subtype.val_injective.addCommGroup (fun x : Completion R M ↦ x.1)
    rfl (fun _ _ ↦ rfl) (fun _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The completion is an `R`-module under its pointwise operations. -/
instance instModule : Module R (Completion R M) :=
  Subtype.val_injective.module R
    { toFun := Subtype.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
    (fun _ _ ↦ rfl)

/-- The completion carries the topology induced by its projections to the discrete quotients. -/
instance instTopologicalSpace : TopologicalSpace (Completion R M) :=
  TopologicalSpace.induced Subtype.val <|
    ⨅ U : {U : Submodule R M // IsOpen (U : Set M)},
      TopologicalSpace.induced (fun f ↦ f U) (⊥ : TopologicalSpace (M ⧸ U.1))

/-- Addition and negation are continuous on the completion. -/
instance instIsTopologicalAddGroup : IsTopologicalAddGroup (Completion R M) := sorry

/-- Scalar multiplication is continuous on the completion under the corresponding hypotheses. -/
instance instContinuousSMul [TopologicalSpace R] [IsTopologicalAddGroup M]
    [ContinuousSMul R M] : ContinuousSMul R (Completion R M) := sorry

/-- The induced topology on the completion is linearly topologized. -/
instance instIsLinearTopology : IsLinearTopology R (Completion R M) where
  hasBasis_submodule' := sorry

/-- The completion is separated in the `T₀` sense. -/
instance instT0Space : T0Space (Completion R M) := sorry

/-- The canonical map sends an element to its compatible family of quotient classes. -/
def of : M →ₗ[R] Completion R M where
  toFun x := ⟨fun U ↦ U.1.mkQ x, fun _ _ h ↦ Submodule.factor_mk h x⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The projection from the completion to the quotient associated to an open submodule. -/
def π (U : Submodule R M) (hU : IsOpen (U : Set M)) : Completion R M →ₗ[R] M ⧸ U where
  toFun f := f.1 ⟨U, hU⟩
  map_add' := fun _ _ ↦ rfl
  map_smul' := fun _ _ ↦ rfl

/-- Evaluating the canonical map at a stage gives the corresponding quotient map. -/
theorem π_of (U : Submodule R M) (hU : IsOpen (U : Set M)) (x : M) :
    π U hU (of x) = U.mkQ x := sorry

/-- Every completed family is compatible with the transition maps between quotient stages. -/
theorem compatible (x : Completion R M) {U U' : Submodule R M}
    (hU : IsOpen (U : Set M)) (hU' : IsOpen (U' : Set M)) (h : U ≤ U') :
    Submodule.factor h (π U hU x) = π U' hU' x := sorry

section mapBetween
variable {N : Type w}
variable [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsLinearTopology R N]

/-- A continuous linear map induces a linear map between the corresponding completions. -/
def map (f : M →ₗ[R] N) (hf : Continuous f) : Completion R M →ₗ[R] Completion R N where
  toFun x :=
    ⟨fun V ↦
      Submodule.mapQ (Submodule.comap f V.1) V.1 f le_rfl
        (x.1 ⟨Submodule.comap f V.1, hf.isOpen_preimage (V.1 : Set N) V.2⟩),
      by
        intro V V' inclusion
        have preimage_inclusion : Submodule.comap f V.1 ≤ Submodule.comap f V'.1 :=
          Submodule.comap_mono inclusion
        have commute (value : M ⧸ Submodule.comap f V.1) :
            Submodule.factor inclusion
                (Submodule.mapQ (Submodule.comap f V.1) V.1 f le_rfl value) =
              Submodule.mapQ (Submodule.comap f V'.1) V'.1 f le_rfl
                (Submodule.factor preimage_inclusion value) := by
          induction value using Submodule.Quotient.induction_on with
          | H representative => rfl
        rw [commute, x.2
          ⟨Submodule.comap f V.1, hf.isOpen_preimage (V.1 : Set N) V.2⟩
          ⟨Submodule.comap f V'.1, hf.isOpen_preimage (V'.1 : Set N) V'.2⟩
          preimage_inclusion]⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    funext V
    exact (Submodule.mapQ (Submodule.comap f V.1) V.1 f le_rfl).map_add _ _
  map_smul' := by
    intro r x
    apply Subtype.ext
    funext V
    exact (Submodule.mapQ (Submodule.comap f V.1) V.1 f le_rfl).map_smul r _

/-- The induced map commutes with the canonical maps from the original modules. -/
theorem map_of (f : M →ₗ[R] N) (hf : Continuous f) (x : M) :
    map f hf (of x) = of (f x) := sorry

end mapBetween

/-- The inclusion of a submodule induces a map between its completion and the ambient completion. -/
def map_subtype (N : Submodule R M) : Completion R N →ₗ[R] Completion R M :=
  map N.subtype continuous_subtype_val

/-- The quotient map induces a map from the ambient completion to the quotient completion. -/
def map_mkQ (N : Submodule R M) [ContinuousAdd M] :
    Completion R M →ₗ[R] Completion R (M ⧸ N) :=
  map N.mkQ N.continuous_mkQ

/-- The completed inclusion agrees with the canonical map on elements of the submodule. -/
theorem map_subtype_of (N : Submodule R M) (x : N) :
    map_subtype N (of x) = of (x : M) := sorry

/-- The canonical map into the completion has dense range. -/
theorem denseRange_of : DenseRange (of : M → Completion R M) := sorry

end Completion

/-- Completion is exact at the ambient term for the inclusion of a submodule and its quotient. -/
theorem exact_completion_subtype_mkQ
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) :
    Function.Injective (Completion.map_subtype N) ∧
      Function.Exact (Completion.map_subtype N) (Completion.map_mkQ N) := sorry

/-- The range of the completed inclusion is the closure of the original submodule image. -/
theorem range_map_subtype_eq_topologicalClosure
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) :
    LinearMap.range (Completion.map_subtype N) =
      (N.map (Completion.of : M →ₗ[R] Completion R M)).topologicalClosure := sorry

/-- A closed quotient of a complete linearly topologized module with a countable
neighborhood basis at zero is complete: its canonical map to its completion is bijective. -/
theorem bijective_completion_of_quotient {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [IsClosed (N : Set M)]
    (hcomplete : Function.Bijective (Completion.of : M → Completion R M))
    [(nhds (0 : M)).IsCountablyGenerated] :
    Function.Bijective (Completion.of : M ⧸ N → Completion R (M ⧸ N)) := sorry

/-- Completion preserves the short exact sequence of a submodule and its quotient
when the ambient module has a countable neighborhood basis at zero. -/
theorem shortExact_completion_subtype_mkQ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [(nhds (0 : M)).IsCountablyGenerated] :
    Function.Injective (Completion.map_subtype N) ∧
      Function.Exact (Completion.map_subtype N) (Completion.map_mkQ N) ∧
      Function.Surjective (Completion.map_mkQ N) := sorry

/-- The completed quotient map is open when the ambient module has a countable
neighborhood basis at zero. -/
theorem isOpenMap_map_mkQ {R : Type u} {M : Type v}
    [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [IsLinearTopology R M]
    (N : Submodule R M) [(nhds (0 : M)).IsCountablyGenerated] :
    IsOpenMap (Completion.map_mkQ N) := sorry

end IsLinearTopology
