/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.ProjectiveDimension
public import ReasLib.RingTheory.Depth.AuslanderBuchsbaum
public import ReasLib.RingTheory.Depth.Surjective
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective dimension over a surjective local map

This leaf owns the Auslander--Buchsbaum equality for a surjective map of Noetherian local
commutative rings.  The algebra-map presentation is the public surface; the underlying
restriction-of-scalars bound is supplied by the sibling generic leaf.

@stack 0929
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace ModuleCat.RestrictScalars.Surjective

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]
variable [IsLocalRing R] [IsNoetherianRing R]

/-- Stacks 0929: a finite `S`-module with finite projective dimension over both `S` and `R` has
finite projective dimension after restriction along a surjective local algebra map. -/
@[stacks 0929 "finite projective dimension after a surjective local restriction"]
theorem projectiveDimension_ne_top
    (M : ModuleCat.{w} S)
    [Module.Finite S M]
    (hsurj : Function.Surjective (algebraMap R S))
    (hS : projectiveDimension (ModuleCat.of R S) ≠ ⊤)
    (hM : projectiveDimension M ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (algebraMap R S)).obj M) ≠ ⊤ := sorry

/-- Stacks 0929: for a finite module over a quotient presented as a surjective local algebra map,
projective dimensions satisfy the additive formula.  The statement includes the zero module as
the canonical `WithBot` extension; a source-facing nonzero specialization is recorded in Chap15.
-/
@[stacks 0929 "projective-dimension additivity for a surjective local restriction"]
theorem projectiveDimension_eq_add
    (M : ModuleCat.{w} S)
    [Module.Finite S M]
    (hsurj : Function.Surjective (algebraMap R S))
    (hS : projectiveDimension (ModuleCat.of R S) ≠ ⊤)
    (hM : projectiveDimension M ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (algebraMap R S)).obj M) =
      projectiveDimension (ModuleCat.of R S) + projectiveDimension M := sorry

end ModuleCat.RestrictScalars.Surjective
