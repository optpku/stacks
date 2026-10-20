/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Tor.Ideal
public import ReasLib.Algebra.Category.ModuleCat.Tor.Notation
public import ReasLib.RingTheory.Flatness.LocalCriterion

/-!
# `Tor` Forms of the Local Flatness Criteria

@stack 00MK
@stack 00ML

This leaf presents the residue-field and quotient `Tor₁` formulations of the
local flatness criterion.  The tensor-injectivity core remains in the parent
`LocalCriterion` leaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped Pointwise

universe u v

namespace Module.Flat

variable {R : Type u} {S : Type v} {M : Type u}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
variable [IsNoetherianRing R] [IsNoetherianRing S]
variable [AddCommGroup M] [Module S M] [Module R M] [IsScalarTower R S M]
variable [Module.Finite S M]

include S

/-- Stacks 00MK: a finite module over a local homomorphism is flat over the source ring when
its first `Tor` with the source residue field vanishes. -/
@[stacks 00MK "local flatness criterion"]
theorem of_isZero_tor_one_residueField
    (hTor : IsZero (Tor₁[R](ResidueField R, M))) :
    Module.Flat R M := sorry

/-- Stacks 00ML: a proper quotient with flat induced module and vanishing first `Tor` detects
flatness of a finite module over a local homomorphism. -/
@[stacks 00ML "variant local flatness criterion"]
theorem of_quotient_flat_of_isZero_tor_one
    (I : Ideal R) (hI : I ≠ ⊤)
    (hTor : IsZero (Tor₁[R](M, R ⧸ I)))
    (hflat : Module.Flat (R ⧸ I) (M ⧸ (I • (⊤ : Submodule R M)))) :
    Module.Flat R M := sorry

omit S

end Module.Flat
