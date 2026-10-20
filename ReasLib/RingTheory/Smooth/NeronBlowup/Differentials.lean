/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Kaehler.Basic
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Residue
public import ReasLib.FieldTheory.Separable.Generated
public import ReasLib.RingTheory.Smooth.AtPrime
public import ReasLib.RingTheory.Smooth.NeronBlowup.Core

/-!
# Differentials of an affine Neron blowup

This file records the localized Kähler-differential map for one affine Neron
blowup and the short exact sequence obtained at its closed center.
-/

@[expose] public section

noncomputable section

open Ideal IsLocalRing
open TensorProduct.AlgebraTensorModule
open scoped TensorProduct

universe u v w

namespace Algebra.DVR.Factorization

variable {R : Type u} {L : Type v}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing L] [IsDomain L] [IsDiscreteValuationRing L]
variable [Algebra R L] [IsExtensionOfDiscreteValuationRings R L]
variable [IsExtensionOfDiscreteValuationRings.WeaklyUnramified R L]

namespace NeronBlowup.Differential

/-- The local special fiber `(A / πA)_p`, expressed as a quotient of the localization at `p`. -/
@[stacks 0BJ4 "old local special fiber"]
abbrev SourceSpecialFiber
    (S : Algebra.DVR.Factorization R L) (π : R) :=
  Localization.AtPrime S.closedIdeal ⧸
    Ideal.span
      ({algebraMap S.mid (Localization.AtPrime S.closedIdeal) (algebraMap R S.mid π)} :
        Set (Localization.AtPrime S.closedIdeal))

/-- The local ring of the affine Neron blowup at its closed center. -/
@[stacks 0BJ4 "new closed-center local ring"]
abbrev TargetLocalRing
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :=
  Localization.AtPrime (S.neronBlowupStage π hπ).closedIdeal

/-- The localization at the new closed center of the base-changed module of differentials
`A' ⊗[A] Ω[A⁄R]`. -/
@[stacks 0BJ4 "base-changed differential source"]
abbrev Source
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :=
  TargetLocalRing S π hπ ⊗[(S.neronBlowupStage π hπ).mid]
    ((S.neronBlowupStage π hπ).mid ⊗[S.mid] Ω[S.mid⁄R])

/-- The localization at the new closed center of `Ω[A'⁄R]`. -/
@[stacks 0BJ4 "blowup differential target"]
abbrev Target
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :=
  TargetLocalRing S π hπ ⊗[(S.neronBlowupStage π hπ).mid]
    Ω[(S.neronBlowupStage π hπ).mid⁄R]

/-- The local special fiber of the affine Neron blowup. -/
@[stacks 0BJ4 "new local special fiber"]
abbrev TargetSpecialFiber
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :=
  TargetLocalRing S π hπ ⧸
    Ideal.span
      ({algebraMap (S.neronBlowupStage π hπ).mid (TargetLocalRing S π hπ)
        (algebraMap R (S.neronBlowupStage π hπ).mid π)} : Set (TargetLocalRing S π hπ))

/-- The localized map on Kähler differentials induced by the transition `A → A'`. -/
@[stacks 0BJ4]
noncomputable def map
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) :
    Source S π hπ →ₗ[TargetLocalRing S π hπ] Target S π hπ :=
  (KaehlerDifferential.mapBaseChange R S.mid
    (S.neronBlowupStage π hπ).mid).baseChange (TargetLocalRing S π hπ)

/-- The localized differential map acts on pure tensors by applying the transition map on
Kahler differentials to the second factor. -/
@[stacks 0BJ4 "localized differential map on pure tensors", simp]
theorem map_tmul
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    (r : TargetLocalRing S π hπ)
    (x : (S.neronBlowupStage π hπ).mid ⊗[S.mid] Ω[S.mid⁄R]) :
    map S π hπ (r ⊗ₜ x) =
      r ⊗ₜ KaehlerDifferential.mapBaseChange R S.mid
        (S.neronBlowupStage π hπ).mid x := sorry

/-- The Kähler short exact sequence associated to one affine Neron blowup.
It records the rank of the special-fiber term and the concrete quotient map;
the standard categorical short complex is derived from these data below. -/
@[stacks 0BJ4 "Kaehler short exact sequence"]
structure Sequence
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π) where
  /-- The number of copies of the new special fiber in the cokernel. -/
  rank : ℕ
  /-- The rank is the Krull dimension of the old local special fiber. -/
  sourceDimension :
    ringKrullDim (SourceSpecialFiber S π) = (rank : WithBot ℕ∞)
  /-- The quotient map to the direct sum of copies of the new special fiber. -/
  toSpecialFiber :
    Target S π hπ →ₗ[TargetLocalRing S π hπ]
      (Fin rank → TargetSpecialFiber S π hπ)
  /-- The localized differential map is injective. -/
  injective : Function.Injective (map S π hπ)
  /-- The two maps are exact at the middle term. -/
  exact : Function.Exact (map S π hπ) toSpecialFiber
  /-- The quotient map is surjective. -/
  surjective : Function.Surjective toSpecialFiber

namespace Sequence

/-- Build the Kähler sequence from its rank, quotient map, and exactness
properties. -/
@[stacks 0BJ4 "Kaehler sequence constructor"]
def of (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    (rank : ℕ)
    (sourceDimension :
      ringKrullDim (SourceSpecialFiber S π) = (rank : WithBot ℕ∞))
    (toSpecialFiber :
      Target S π hπ →ₗ[TargetLocalRing S π hπ]
        (Fin rank → TargetSpecialFiber S π hπ))
    (injective : Function.Injective (map S π hπ))
    (exact : Function.Exact (map S π hπ) toSpecialFiber)
    (surjective : Function.Surjective toSpecialFiber) :
    Sequence S π hπ :=
  { rank := rank
    sourceDimension := sourceDimension
    toSpecialFiber := toSpecialFiber
    injective := injective
    exact := exact
    surjective := surjective }

/-- The dimension and function-level exactness properties carried by the
Kähler sequence. -/
@[stacks 0BJ4 "Kaehler sequence specification"]
theorem spec {S : Algebra.DVR.Factorization R L} {π : R}
    {hπ : Irreducible π} (E : Sequence S π hπ) :
    ringKrullDim (SourceSpecialFiber S π) = (E.rank : WithBot ℕ∞) ∧
      Function.Injective (map S π hπ) ∧
      Function.Exact (map S π hπ) E.toSpecialFiber ∧
      Function.Surjective E.toSpecialFiber := sorry

/-- The standard module-category short complex underlying the Kähler
sequence. -/
@[stacks 0BJ4 "Kaehler short complex"]
def shortComplex {S : Algebra.DVR.Factorization R L} {π : R}
    {hπ : Irreducible π} (E : Sequence S π hπ) :
    CategoryTheory.ShortComplex
      (ModuleCat.{w} (TargetLocalRing S π hπ)) :=
  CategoryTheory.ShortComplex.moduleCatMk (map S π hπ)
    E.toSpecialFiber E.exact.linearMap_comp_eq_zero

/-- The standard short complex underlying the Kähler sequence is short
exact. -/
@[stacks 0BJ4 "Kaehler categorical short exactness"]
theorem shortExact {S : Algebra.DVR.Factorization R L} {π : R}
    {hπ : Irreducible π} (E : Sequence S π hπ) :
    E.shortComplex.ShortExact := sorry

end Sequence

end NeronBlowup.Differential

/-- Lemma 16.4.3 (1) (tag 0BJ4): if the original factorization is smooth at its closed center
and the residue-field extension is separable, then one affine Neron blowup is smooth at its new
closed center. -/
@[stacks 0BJ4]
theorem NeronBlowup.smoothAtClosedCenter
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    [Algebra.IsSeparableOver (ResidueField R) (ResidueField L)]
    (hsmooth : Algebra.SmoothAtPrime R S.mid S.closedPoint) :
    Algebra.SmoothAtPrime R (S.neronBlowupStage π hπ).mid
      (S.neronBlowupStage π hπ).closedPoint := sorry

/-- Lemma 16.4.3 (2) (tag 0BJ4): at the new closed center, the map on Kähler
differentials induced by one affine Neron blowup belongs to a short exact
sequence whose cokernel rank is the dimension of the old local special fiber. -/
@[stacks 0BJ4 "existence of the Kaehler sequence"]
theorem NeronBlowup.Differential.Sequence.nonempty
    (S : Algebra.DVR.Factorization R L) (π : R) (hπ : Irreducible π)
    [Algebra.IsSeparableOver (ResidueField R) (ResidueField L)]
    (hsmooth : Algebra.SmoothAtPrime R S.mid S.closedPoint) :
    Nonempty (NeronBlowup.Differential.Sequence S π hπ) := sorry

end Algebra.DVR.Factorization
