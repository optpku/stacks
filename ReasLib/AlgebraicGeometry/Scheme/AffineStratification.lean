/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Order.KrullDimension
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.LocallyFinite
public import ReasLib.AlgebraicGeometry.Scheme.LocallyClosedReduction
public import ReasLib.Topology.Stratification.Indexed

/-!
# Affine stratifications

Affine stratifications are locally finite ordered locally closed stratifications whose reduced
strata and canonical immersions into the ambient scheme are affine. Finite affine stratifications
add a finite index order, which determines the affine stratification number of a nonempty
quasi-compact quasi-separated scheme.
-/

@[expose] public section

open Set TopologicalSpace

universe u v w

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- An affine stratification is a locally finite indexed stratification by nonempty subsets
whose canonical reduced stratum schemes and canonical immersions into the ambient scheme are
affine. -/
class IsAffineStratification {I : Type v} [PartialOrder I] (strata : I → Set X) : Prop
    extends IsStratification strata where
  /-- The family of strata is locally finite. -/
  locallyFinite : LocallyFinite strata
  /-- Every indexed stratum is nonempty. -/
  strata_nonempty (i : I) : (strata i).Nonempty
  /-- Every canonical reduced stratum scheme is affine. -/
  stratum_isAffine (i : I) :
    IsAffine (LocallyClosedReduction.scheme
      ⟨strata i, toIsStratification.locallyClosed i⟩)
  /-- Every canonical immersion of a reduced stratum into the ambient scheme is affine. -/
  stratum_ι_isAffineHom (i : I) :
    IsAffineHom (LocallyClosedReduction.ι
      ⟨strata i, toIsStratification.locallyClosed i⟩)

namespace IsAffineStratification

variable {I : Type v} [PartialOrder I] {strata : I → Set X}

/-- Construct an affine stratification from its indexed stratification, local finiteness,
nonemptiness, and the two pointwise affine conditions. -/
theorem ofStrata (hstrata : IsStratification strata) (h_locallyFinite : LocallyFinite strata)
    (h_nonempty : ∀ i, (strata i).Nonempty)
    (h_affine : ∀ i, IsAffine (LocallyClosedReduction.scheme
      ⟨strata i, hstrata.locallyClosed i⟩))
    (h_affineHom : ∀ i, IsAffineHom (LocallyClosedReduction.ι
      ⟨strata i, hstrata.locallyClosed i⟩)) :
    IsAffineStratification strata := sorry

/-- The indexed stratification, local finiteness, nonemptiness, affine-scheme, and
affine-morphism conditions defining an affine stratification. -/
theorem spec [h : IsAffineStratification strata] :
    IsStratification strata ∧
      LocallyFinite strata ∧
      (∀ i, (strata i).Nonempty) ∧
      (∀ i, IsAffine (LocallyClosedReduction.scheme
        ⟨strata i, h.toIsStratification.locallyClosed i⟩)) ∧
      ∀ i, IsAffineHom (LocallyClosedReduction.ι
        ⟨strata i, h.toIsStratification.locallyClosed i⟩) := sorry

/-- Every canonical reduced stratum scheme in an affine stratification is affine. -/
instance stratumIsAffine [h : IsAffineStratification strata] (i : I) :
    IsAffine (LocallyClosedReduction.scheme
      ⟨strata i, h.toIsStratification.locallyClosed i⟩) := sorry

/-- Every canonical immersion of a reduced stratum in an affine stratification is affine. -/
instance stratumιIsAffineHom [h : IsAffineStratification strata] (i : I) :
    IsAffineHom (LocallyClosedReduction.ι
      ⟨strata i, h.toIsStratification.locallyClosed i⟩) := sorry

/-- Reindexing an affine stratification along an order isomorphism preserves the affine
stratification property. -/
instance reindex {J : Type w} [PartialOrder J] (e : J ≃o I)
    [IsAffineStratification strata] :
    IsAffineStratification (strata ∘ e) := sorry

end IsAffineStratification

/-- A finite affine stratification of a scheme is a finite ordered locally closed stratification
with nonempty strata such that every reduced stratum and its canonical immersion are affine. -/
structure FiniteAffineStratification (X : Scheme.{u}) extends FiniteStratification.{u, v} X where
  /-- Every stratum is nonempty. -/
  strata_nonempty (i : index) : (strata i).Nonempty
  /-- Every canonical reduced stratum scheme is affine. -/
  stratum_isAffine (i : index) :
    IsAffine (LocallyClosedReduction.scheme
      ⟨strata i, isStratification.locallyClosed i⟩)
  /-- Every canonical immersion of a reduced stratum into the ambient scheme is affine. -/
  stratum_ι_isAffineHom (i : index) :
    IsAffineHom (LocallyClosedReduction.ι
      ⟨strata i, isStratification.locallyClosed i⟩)

namespace FiniteAffineStratification

variable {X : Scheme.{u}}

/-- Construct a finite affine stratification from a finite ordered family satisfying its
topological and affine conditions. -/
def ofStrata {I : Type v} [Finite I] [PartialOrder I] (strata : I → Set X)
    (hstrata : IsStratification strata) (h_nonempty : ∀ i, (strata i).Nonempty)
    (h_affine : ∀ i, IsAffine (LocallyClosedReduction.scheme
      ⟨strata i, hstrata.locallyClosed i⟩))
    (h_affineHom : ∀ i, IsAffineHom (LocallyClosedReduction.ι
      ⟨strata i, hstrata.locallyClosed i⟩)) :
    FiniteAffineStratification X where
  toFiniteStratification := FiniteStratification.ofStrata strata hstrata
  strata_nonempty := h_nonempty
  stratum_isAffine := h_affine
  stratum_ι_isAffineHom := h_affineHom

/-- The defining topological, nonemptiness, affine-scheme, and affine-morphism conditions of a
finite affine stratification. -/
theorem spec (S : FiniteAffineStratification.{u, v} X) :
    @IsStratification X _ S.index S.instPartialOrder S.strata ∧
      (∀ i, (S.strata i).Nonempty) ∧
      (∀ i, IsAffine (LocallyClosedReduction.scheme
        ⟨S.strata i, @IsStratification.locallyClosed X _ S.index S.instPartialOrder
          S.strata S.isStratification i⟩)) ∧
      ∀ i, IsAffineHom (LocallyClosedReduction.ι
        ⟨S.strata i, @IsStratification.locallyClosed X _ S.index S.instPartialOrder
          S.strata S.isStratification i⟩) := sorry

/-- The underlying finite stratification of `ofStrata` is the supplied indexed family. -/
theorem ofStrata_toFiniteStratification {I : Type v} [Finite I] [PartialOrder I]
    (strata : I → Set X) (hstrata : IsStratification strata)
    (h_nonempty : ∀ i, (strata i).Nonempty)
    (h_affine : ∀ i, IsAffine (LocallyClosedReduction.scheme
      ⟨strata i, hstrata.locallyClosed i⟩))
    (h_affineHom : ∀ i, IsAffineHom (LocallyClosedReduction.ι
      ⟨strata i, hstrata.locallyClosed i⟩)) :
    (ofStrata strata hstrata h_nonempty h_affine h_affineHom).toFiniteStratification =
      FiniteStratification.ofStrata strata hstrata := sorry

/-- The Krull dimension of the explicitly stored finite index order. -/
noncomputable def indexDimension (S : FiniteAffineStratification.{u, v} X) : WithBot ℕ∞ :=
  @Order.krullDim S.index S.instPartialOrder.toPreorder

/-- Order isomorphisms from the explicitly stored index order to `Fin (n + 1)`. -/
abbrev FinIndexOrderIso (S : FiniteAffineStratification.{u, v} X) (n : ℕ) :=
  @OrderIso S.index (Fin (n + 1)) S.instPartialOrder.toLE inferInstance

/-- `HasLength X n` means that `X` has a finite affine stratification whose index order has
Krull dimension `n`. -/
def HasLength (X : Scheme.{u}) (n : ℕ) : Prop :=
  ∃ S : FiniteAffineStratification.{u, 0} X,
    indexDimension S = (n : WithBot ℕ∞)

/-- The existential characterization of attainable finite affine stratification length. -/
theorem hasLength_iff (X : Scheme.{u}) (n : ℕ) :
    HasLength X n ↔ ∃ S : FiniteAffineStratification.{u, 0} X,
      indexDimension S = (n : WithBot ℕ∞) := sorry

/-- `HasFinIndex X n` means that `X` has a finite affine stratification whose stored index order
is order-isomorphic to `Fin (n + 1)`. -/
def HasFinIndex (X : Scheme.{u}) (n : ℕ) : Prop :=
  ∃ S : FiniteAffineStratification.{u, 0} X,
    Nonempty (FinIndexOrderIso S n)

/-- The existential characterization of finite affine stratifications indexed by
`Fin (n + 1)` up to order isomorphism. -/
theorem hasFinIndex_iff (X : Scheme.{u}) (n : ℕ) :
    HasFinIndex X n ↔ ∃ S : FiniteAffineStratification.{u, 0} X,
      Nonempty (FinIndexOrderIso S n) := sorry

/-- A finite affine stratification with index-order Krull dimension `n` can be reindexed by
`Fin (n + 1)`. -/
theorem hasFinIndex_of_krullDim_eq (S : FiniteAffineStratification.{u, v} X) {n : ℕ}
    (h_length : indexDimension S = (n : WithBot ℕ∞)) : HasFinIndex X n := sorry

/-- A scheme admits a finite affine stratification if and only if it is quasi-compact and
quasi-separated. -/
theorem nonempty_iff_compactSpace_and_quasiSeparatedSpace (X : Scheme.{u}) :
    Nonempty (FiniteAffineStratification.{u, 0} X) ↔
      CompactSpace X ∧ QuasiSeparatedSpace X := sorry

/-- A finite affine stratification of length `n` exists if and only if one exists whose index
order is isomorphic to `Fin (n + 1)`. -/
theorem hasLength_iff_hasFinIndex (X : Scheme.{u}) (n : ℕ) :
    HasLength X n ↔ HasFinIndex X n := sorry

/-- The affine stratification number is the least attainable length of a finite affine
stratification. -/
noncomputable def number (X : Scheme.{u}) [Nonempty X] [CompactSpace X]
    [QuasiSeparatedSpace X] : ℕ :=
  sInf {n | HasLength X n}

/-- The affine stratification number is the least attainable stratification length. -/
theorem number_isLeast (X : Scheme.{u}) [Nonempty X] [CompactSpace X]
    [QuasiSeparatedSpace X] : IsLeast {n | HasLength X n} (number X) := sorry

/-- The affine stratification number is attained by a finite affine stratification. -/
theorem number_hasLength (X : Scheme.{u}) [Nonempty X] [CompactSpace X]
    [QuasiSeparatedSpace X] : HasLength X (number X) := sorry

/-- Every attainable length bounds the affine stratification number from above. -/
theorem number_le {X : Scheme.{u}} [Nonempty X] [CompactSpace X] [QuasiSeparatedSpace X]
    {n : ℕ} (hn : HasLength X n) : number X ≤ n := sorry

/-- The affine stratification number is attained by a stratification whose index order is
isomorphic to `Fin (number X + 1)`. -/
theorem number_hasFinIndex (X : Scheme.{u}) [Nonempty X] [CompactSpace X]
    [QuasiSeparatedSpace X] : HasFinIndex X (number X) := sorry

end FiniteAffineStratification

end AlgebraicGeometry.Scheme
