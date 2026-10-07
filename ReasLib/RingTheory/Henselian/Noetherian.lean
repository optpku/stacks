module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Completion.Flat
public import ReasLib.RingTheory.Henselian.FormallyEtale
public import ReasLib.RingTheory.Henselian.Henselization.Completion

@[expose] public section

/-!
# Noetherianity and henselization

@stack 06LJ

Noetherianity is invariant under passing from a local ring to either a henselization or a strict
henselization. The individual ascent results live on their respective owners; this file records
their symmetric, source-independent interface.
-/

universe u v w

open IsLocalRing
open scoped TensorProduct

namespace Henselization

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {Rh : Type v} [CommRing Rh] [Algebra R Rh] [IsHenselizationOf R Rh]
variable {Rsh : Type w} [CommRing Rsh] [Algebra R Rsh] [IsStrictHenselizationOf R Rsh]

/-- Lemma 15.45.3, equivalence (tag `06LJ`): Noetherianity of a local ring, of any
henselization, and of any strict henselization are equivalent. -/
@[stacks 06LJ "equivalence (1)-(3), Noetherianity is invariant under henselization"]
theorem noetherian_tfae :
    List.TFAE [IsNoetherianRing R, IsNoetherianRing Rh, IsNoetherianRing Rsh] := sorry

/-- Lemma 15.45.3 (a) (tag `06LJ`): the maximal-ideal completions of a henselization and a strict
henselization are Noetherian complete local rings. The local Noetherian instances in the result
are the source-derived consequences of part (1), kept local because their base rings are not
recoverable from the completion types. -/
@[stacks 06LJ "(a) completed henselizations are Noetherian complete local rings"]
theorem completions_noetherian_complete_local [IsNoetherianRing R] :
    let _ : IsNoetherianRing Rh :=
      IsHenselizationOf.isNoetherianRing (R := R) (S := Rh)
    let _ : IsNoetherianRing Rsh :=
      IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
    (IsNoetherianRing (AdicCompletion (maximalIdeal Rh) Rh) ∧
      IsLocalRing (AdicCompletion (maximalIdeal Rh) Rh) ∧
      IsAdicComplete
        (maximalIdeal (AdicCompletion (maximalIdeal Rh) Rh))
        (AdicCompletion (maximalIdeal Rh) Rh)) ∧
    (IsNoetherianRing (AdicCompletion (maximalIdeal Rsh) Rsh) ∧
      IsLocalRing (AdicCompletion (maximalIdeal Rsh) Rsh) ∧
      IsAdicComplete
        (maximalIdeal (AdicCompletion (maximalIdeal Rsh) Rsh))
        (AdicCompletion (maximalIdeal Rsh) Rsh)) := sorry

/-- Lemma 15.45.3 (c) (tag `06LJ`): the structural maps from a henselization and a strict
henselization to their maximal-ideal completions are flat. -/
@[stacks 06LJ "(c) flatness of the completion maps"]
theorem completion_algebraMaps_flat [IsNoetherianRing R] :
    RingHom.Flat (algebraMap Rh (AdicCompletion (maximalIdeal Rh) Rh)) ∧
      RingHom.Flat (algebraMap Rsh (AdicCompletion (maximalIdeal Rsh) Rsh)) := sorry

/-- Lemma 15.45.3 (d) (tag `06LJ`): the canonical map from the completion of the base to the
completion of a strict henselization is formally smooth for the target maximal-ideal topology. -/
@[stacks 06LJ "(d) formal smoothness of the strict completion map"]
theorem strictCompletionMap_formallySmooth [IsNoetherianRing R] :
    let _ : IsNoetherianRing Rsh :=
      IsStrictHenselizationOf.isNoetherianRing (R := R) (S := Rsh)
    (AdicCompletion.mapLocal (algebraMap R Rsh)).formally_smooth_for_adic
      (maximalIdeal (AdicCompletion (maximalIdeal Rsh) Rsh)) := sorry

section StrictBaseChange

variable [Algebra Rh Rsh] [IsScalarTower R Rh Rsh]

/-- Lemma 15.45.3 (e) (tag `06LJ`): after using the canonical henselization comparison to make
the base completion an `Rh`-algebra, its tensor product with `Rsh` is a strict henselization of
the completed base. This is the owner-level form of
`(Rhat)sh = Rhat ⊗[Rh] Rsh`. -/
@[stacks 06LJ "(e) strict henselization after completion"]
theorem strictBaseChange_isStrictHenselization [IsNoetherianRing R]
    (iota : IsHenselizationOf.Completion.Comparison (R := R) (Rh := Rh)) :
    let _ : Algebra Rh (AdicCompletion (maximalIdeal R) R) :=
      iota.toAlgHom.toRingHom.toAlgebra
    IsStrictHenselizationOf (AdicCompletion (maximalIdeal R) R)
      (AdicCompletion (maximalIdeal R) R ⊗[Rh] Rsh) := sorry

/-- The right tensor-factor map in the strict base-change model is local. This proof-only bridge
lets the canonical completion map be stated without registering a comparison-dependent global
instance. -/
theorem strictBaseChange_includeRight_isLocal [IsNoetherianRing R]
    (iota : IsHenselizationOf.Completion.Comparison (R := R) (Rh := Rh)) :
    let _ : Algebra Rh (AdicCompletion (maximalIdeal R) R) :=
      iota.toAlgHom.toRingHom.toAlgebra
    IsLocalHom (Algebra.TensorProduct.includeRight.toRingHom :
      Rsh →+* AdicCompletion (maximalIdeal R) R ⊗[Rh] Rsh) := sorry

/-- Lemma 15.45.3 (f) (tag `06LJ`): completing the strict base-change model gives the same
completion as `Rsh`; concretely, the completion map induced by the right tensor-factor inclusion
is bijective. -/
@[stacks 06LJ "(f) completion of the strict base-change model"]
theorem strictBaseChange_completionMap_bijective [IsNoetherianRing R]
    (iota : IsHenselizationOf.Completion.Comparison (R := R) (Rh := Rh)) :
    let _ : Algebra Rh (AdicCompletion (maximalIdeal R) R) :=
      iota.toAlgHom.toRingHom.toAlgebra
    let T := AdicCompletion (maximalIdeal R) R ⊗[Rh] Rsh
    let _ : IsStrictHenselizationOf (AdicCompletion (maximalIdeal R) R) T :=
      strictBaseChange_isStrictHenselization iota
    let f : Rsh →+* T := Algebra.TensorProduct.includeRight.toRingHom
    let _ : IsLocalHom f := strictBaseChange_includeRight_isLocal iota
    Function.Bijective (AdicCompletion.mapLocal f) := sorry

end StrictBaseChange

end Henselization
