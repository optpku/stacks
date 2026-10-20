/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.CategoryTheory.Monoidal.Tor
public import ReasLib.RingTheory.DividedPowers.Tate.Projective

/-!
# Tor computed by a Tate resolution

This file is the additive derived-functor boundary for Tate resolutions.  It computes
`Tor` from the explicit projective resolution underlying a Tate resolution, without yet
transporting the multiplicative or divided-power structure to the canonical `Tor` objects.

The resolution owner and its projective-resolution API allow the base ring and target algebra
to live in separate universes.  This leaf specializes them to one universe because Mathlib's
current monoidal structure on `ModuleCat` requires the coefficient ring and module carriers at
the same universe level.
-/

@[expose] public section

noncomputable section

open CategoryTheory HomologicalComplex
open CategoryTheory.MonoidalCategory

universe u v

namespace TateResolution

variable {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
variable {J : Type v} {pi0 : MvPolynomial J R →ₐ[R] T}

/-- The chain complex obtained by tensoring a module with the natural-degree complex of a
Tate resolution. -/
abbrev tensorComplex (A : TateResolution.{u, v} pi0) (M : ModuleCat R) :
    ChainComplex (ModuleCat R) ℕ :=
  ((tensorLeft M).mapHomologicalComplex (ComplexShape.down ℕ)).obj A.naturalComplex

/-- Tag 09PQ: a Tate resolution of `T` computes `CategoryTheory.Tor (ModuleCat R) n`
at `(M, ModuleCat.of R T)` for every `R`-module `M`.  This is the canonical additive
comparison; the multiplicative and divided-power transport needed for the full statement
of Tag 09PQ belongs to a later layer. -/
@[stacks 09PQ "Tor computed by a Tate resolution"]
noncomputable abbrev torIso (A : TateResolution.{u, v} pi0) (M : ModuleCat R) (n : ℕ) :
    (((CategoryTheory.Tor (ModuleCat R) n).obj M).obj (ModuleCat.of R T)) ≅
      (A.tensorComplex M).homology n :=
  A.toProjectiveResolution.isoLeftDerivedObj (tensorLeft M) n

end TateResolution
