/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Topology.Constructible
public import Mathlib.Topology.LocallyFinite
public import ReasLib.Topology.Constructible.LocallyClosed
public import ReasLib.Topology.Constructible.LocallyConstructible
public import ReasLib.Topology.ConstructibleTopology.Spectral

@[expose] public section

open Topology
open scoped Set.Notation

universe u v

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {E : Set X}

/-- A subset of a scheme is locally constructible if and only if its trace on every affine open
subscheme is constructible. -/
theorem isLocallyConstructible_iff_forall_isAffineOpen :
    IsLocallyConstructible E ↔
      ∀ U : X.Opens, IsAffineOpen U → IsConstructible ((U : Set X) ↓∩ E) := sorry

/-- The trace of a locally constructible subset on an affine open subscheme is constructible. -/
theorem IsLocallyConstructible.isConstructible_affineOpen
    (hE : IsLocallyConstructible E) (U : X.affineOpens) :
    IsConstructible ((U : Set X) ↓∩ E) := sorry

/-- A locally constructible subset of a scheme is a neighborhood of any point whose every
generalization belongs to the subset. -/
theorem IsLocallyConstructible.mem_nhds_of_generizations_subset
    {X : Scheme.{u}} {E : Set X} {x : X} (hE : IsLocallyConstructible E)
    (hx : {x' : X | x' ⤳ x} ⊆ E) :
    E ∈ 𝓝 x := sorry

/-- An indexed locally closed partition of a scheme into retrocompact parts is locally finite if
and only if every part is locally constructible. -/
theorem locallyFinite_iff_forall_isLocallyConstructible_of_retrocompact
    {I : Type v} {parts : I → Set X} (hparts : IndexedPartition parts)
    (hclosed : ∀ i, IsLocallyClosed (parts i)) (hretro : ∀ i, IsRetrocompact (parts i)) :
    LocallyFinite parts ↔ ∀ i, IsLocallyConstructible (parts i) := sorry

/-- At a generic point of an irreducible component of a scheme, a locally constructible subset
is a neighborhood exactly when it contains that point. -/
theorem IsLocallyConstructible.mem_nhds_iff_of_mem_genericPoints
    {X : Scheme.{u}} {E : Set X} {xi : X} (hE : IsLocallyConstructible E)
    (hxi : xi ∈ genericPoints X) :
    E ∈ 𝓝 xi ↔ xi ∈ E := sorry

/-- At a generic point of an irreducible component of a scheme, the complement of a locally
constructible subset is a neighborhood exactly when the subset omits that point. -/
theorem IsLocallyConstructible.compl_mem_nhds_iff_of_mem_genericPoints
    {X : Scheme.{u}} {E : Set X} {xi : X} (hE : IsLocallyConstructible E)
    (hxi : xi ∈ genericPoints X) :
    Eᶜ ∈ 𝓝 xi ↔ xi ∉ E := sorry

/-- A locally constructible subset containing a generic point of an irreducible component is a
neighborhood of that point. -/
theorem IsLocallyConstructible.mem_nhds_of_mem_genericPoints
    {X : Scheme.{u}} {E : Set X} {xi : X} (hE : IsLocallyConstructible E)
    (hxi : xi ∈ genericPoints X) (hmem : xi ∈ E) :
    E ∈ 𝓝 xi :=
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.mem_nhds_iff_of_mem_genericPoints
    hE hxi).2 hmem

/-- The complement of a locally constructible subset omitting a generic point of an irreducible
component is a neighborhood of that point. -/
theorem IsLocallyConstructible.compl_mem_nhds_of_not_mem_genericPoints
    {X : Scheme.{u}} {E : Set X} {xi : X} (hE : IsLocallyConstructible E)
    (hxi : xi ∈ genericPoints X) (hnotmem : xi ∉ E) :
    Eᶜ ∈ 𝓝 xi :=
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.compl_mem_nhds_iff_of_mem_genericPoints
    hE hxi).2 hnotmem

end AlgebraicGeometry.Scheme
