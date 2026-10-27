/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.KrullDimension
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Topology.Sets.OpenCover
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.IrreducibleCloseds.Open
public import ReasLib.Topology.IrreducibleCloseds.Subspace

/-!
# Catenary Topological Spaces

This module owns catenarity expressed through intervals of irreducible closed subsets and its
basic transport and locality API.
-/

@[expose] public section

universe u v

open Set Order

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- The relative codimension of comparable irreducible closed subsets. The comparison proof is
used directly to select the initial element of the interval, so no auxiliary `Fact` instance is
needed. -/
noncomputable def codimBetween (T T' : IrreducibleCloseds X) (hTT' : T ≤ T') : ℕ∞ :=
  coheight (⟨T, le_rfl, hTT'⟩ : Set.Icc T T')

/-- Relative codimension is the Krull dimension of the corresponding interval. -/
theorem codimBetween_eq_krullDim {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' = krullDim (Set.Icc T T') := sorry

/-- An order isomorphism of irreducible closed subsets preserves relative codimension. -/
theorem codimBetween_orderIso {Y : Type v} [TopologicalSpace Y]
    (e : IrreducibleCloseds X ≃o IrreducibleCloseds Y)
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween (e T) (e T') (e.monotone hTT') =
      codimBetween T T' hTT' := sorry

/-- A closed embedding preserves relative codimension of comparable irreducible closed subsets. -/
theorem _root_.Topology.IsClosedEmbedding.codimBetween_map_eq
    {Y : Type v} [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsClosedEmbedding f)
    {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween (IrreducibleCloseds.map f hf.continuous T)
        (IrreducibleCloseds.map f hf.continuous T')
        (IrreducibleCloseds.map_mono hf.continuous hTT') =
      codimBetween T T' hTT' := sorry

/-- Passing from a closed subspace to the ambient space preserves relative codimension between
irreducible closed subsets of that subspace. -/
theorem codimBetween_subtype_eq_of_isClosed
    {S : Set X} (hS : IsClosed S) {T T' : IrreducibleCloseds S} (hTT' : T ≤ T') :
    codimBetween T T' hTT' =
      codimBetween
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T)
        (IrreducibleCloseds.map (Subtype.val : S → X) continuous_subtype_val T')
        (IrreducibleCloseds.map_mono continuous_subtype_val hTT') := sorry

/-- A topological space is catenary if every comparable pair of irreducible
closed subsets has finite relative codimension and every maximal chain in that interval has the
prescribed common length. -/
@[stacks 02I1]
class CatenarySpace (X : Type u) [TopologicalSpace X] : Prop where
  /-- Comparable irreducible closed subsets have finite relative codimension. -/
  finite_codimBetween {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' < ⊤
  /-- Every maximal chain in an irreducible-closed interval has the prescribed common length. -/
  maximalIrreducibleClosedChainsHaveLength {T T' : IrreducibleCloseds X}
      (hTT' : T ≤ T') (s : Set (Set.Icc T T')) (hs : IsMaxChain (· ≤ ·) s) :
      s.encard = ENat.toNat (codimBetween T T' hTT') + 1

/-- The two defining conditions bundled by `CatenarySpace`: finite relative codimension and the
prescribed cardinality of every maximal chain in each irreducible-closed interval. -/
theorem catenarySpace_iff :
    CatenarySpace X ↔
      (∀ ⦃T T' : IrreducibleCloseds X⦄ (hTT' : T ≤ T'), codimBetween T T' hTT' < ⊤) ∧
      ∀ ⦃T T' : IrreducibleCloseds X⦄ (hTT' : T ≤ T')
        (s : Set (Set.Icc T T')) (hs : IsMaxChain (· ≤ ·) s),
        s.encard = ENat.toNat (codimBetween T T' hTT') + 1 := sorry

/-- Catenarity transports along an order isomorphism of irreducible closed subsets. -/
theorem CatenarySpace.of_irreducibleClosedsOrderIso
    {Y : Type v} [TopologicalSpace Y]
    (hX : CatenarySpace X) (e : IrreducibleCloseds X ≃o IrreducibleCloseds Y) :
    CatenarySpace Y := sorry

/-- Catenarity transports across a homeomorphism. -/
theorem _root_.Homeomorph.catenarySpace
    {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) [CatenarySpace X] :
    CatenarySpace Y := sorry

/-- Homeomorphic spaces are catenary simultaneously. -/
theorem _root_.Homeomorph.catenarySpace_iff
    {Y : Type v} [TopologicalSpace Y] (e : X ≃ₜ Y) :
    CatenarySpace X ↔ CatenarySpace Y := sorry

namespace CatenarySpace

/-- In a catenary space, relative codimension is additive along chains of irreducible closed
subsets. -/
theorem codimBetween_additive [CatenarySpace X] {T T' T'' : IrreducibleCloseds X}
    (hTT' : T ≤ T') (hT'T'' : T' ≤ T'') :
    codimBetween T T'' (hTT'.trans hT'T'') =
      codimBetween T T' hTT' + codimBetween T' T'' hT'T'' := sorry

end CatenarySpace

namespace IsOpenCover

/-- Catenarity can be checked on every member of a fixed open cover. -/
theorem catenarySpace_iff {ι : Type v} {U : ι → Opens X} (hU : IsOpenCover U) :
    CatenarySpace X ↔ ∀ i, CatenarySpace (U i) := sorry

end IsOpenCover

/-- A topological space is catenary if and only if it has an open covering by
catenary open subspaces. -/
@[stacks 02I2 "catenarity is local for an open covering"]
theorem catenarySpace_iff_hasOpenCoverByCatenarySpaces :
    CatenarySpace X ↔
      ∃ (ι : Type v) (U : ι → Opens X), IsOpenCover U ∧ ∀ i, CatenarySpace (U i) := sorry

/-- Every locally closed subspace of a catenary topological space is catenary. -/
@[stacks 02I2 "locally closed subspaces of catenary spaces are catenary"]
protected theorem _root_.IsLocallyClosed.catenarySpace [CatenarySpace X] {Y : Set X}
    (hY : IsLocallyClosed Y) : CatenarySpace Y := sorry

/-- Every bundled open subspace of a catenary space inherits the canonical catenary instance. -/
instance instCatenarySpaceOpens (U : Opens X) [CatenarySpace X] : CatenarySpace U := sorry

/-- A topological space is catenary if and only if relative codimension between
comparable irreducible closed subsets is finite and additive along chains. -/
@[stacks 02I6]
theorem catenarySpace_iff_finite_codimBetween_and_codimBetween_additive :
    CatenarySpace X ↔
      (∀ ⦃T T' : IrreducibleCloseds X⦄ (hTT' : T ≤ T'), codimBetween T T' hTT' < ⊤) ∧
      (∀ ⦃T T' T'' : IrreducibleCloseds X⦄
          (hTT' : T ≤ T') (hT'T'' : T' ≤ T''),
          codimBetween T T'' (hTT'.trans hT'T'') =
            codimBetween T T' hTT' + codimBetween T' T'' hT'T'') := sorry

end TopologicalSpace
