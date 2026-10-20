/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Topology.Constructible
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open Topology

universe u

/- Lemma 28.2.2: if a locally constructible subset contains a generic point of an irreducible
component of a scheme, then it is a neighborhood of that point. -/
@[stacks 0AAW] #check
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.mem_nhds_of_mem_genericPoints :
    ∀ {X : Scheme.{u}} {E : Set X} {ξ : X}, IsLocallyConstructible E →
      ξ ∈ genericPoints X → ξ ∈ E → E ∈ 𝓝 ξ)

#check
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.compl_mem_nhds_of_not_mem_genericPoints :
    ∀ {X : Scheme.{u}} {E : Set X} {ξ : X}, IsLocallyConstructible E →
      ξ ∈ genericPoints X → ξ ∉ E → Eᶜ ∈ 𝓝 ξ)

#check
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.mem_nhds_iff_of_mem_genericPoints :
    ∀ {X : Scheme.{u}} {E : Set X} {ξ : X}, IsLocallyConstructible E →
      ξ ∈ genericPoints X → (E ∈ 𝓝 ξ ↔ ξ ∈ E))

#check
  (AlgebraicGeometry.Scheme.IsLocallyConstructible.compl_mem_nhds_iff_of_mem_genericPoints :
    ∀ {X : Scheme.{u}} {E : Set X} {ξ : X}, IsLocallyConstructible E →
      ξ ∈ genericPoints X → (Eᶜ ∈ 𝓝 ξ ↔ ξ ∉ E))
