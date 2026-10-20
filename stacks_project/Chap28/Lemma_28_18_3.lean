/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.BasicOpen
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open Opposite
open scoped AlgebraicGeometry

universe u

/- Lemma 28.18.3: let `X` be a quasi-compact and quasi-separated scheme and let
`f : Γ(X, ⊤)`. If `X.basicOpen f` is affine, then the canonical morphism from `X` to the
spectrum of its global sections restricts to an isomorphism from `X.basicOpen f` onto
`PrimeSpectrum.basicOpen f`. -/
@[stacks 01P8] #check
  (AlgebraicGeometry.isIso_restrict_toSpecΓ_basicOpen_of_isAffineOpen :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (f : Γ(X, ⊤)) (_ : IsAffineOpen (X.basicOpen f)),
      CategoryTheory.IsIso (X.toSpecΓ ∣_ PrimeSpectrum.basicOpen f))
