/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.GScheme.Locality

/-!
# Local criteria for G-schemes

A scheme is a G-scheme if and only if every affine-open section ring is a
G-ring, equivalently if some affine open cover has G-ring section rings, and
equivalently if some open cover consists of G-scheme open subschemes. Every
open subscheme of a G-scheme is a G-scheme.

This terminology is nonstandard: a G-scheme here is not a scheme equipped
with an action of a finite group or group scheme.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma [Stacks 0HA5] (1): a scheme is a G-scheme if and only if the section
ring of every affine open is a G-ring. -/
@[stacks 0HA5]
#check (AlgebraicGeometry.Scheme.gScheme_iff_forall_affineOpen :
  ∀ X : Scheme.{u},
    X.GScheme ↔ ∀ U : X.affineOpens, IsGRing Γ(X, U))

/- Lemma [Stacks 0HA5] (2): a scheme is a G-scheme if and only if some affine
open cover has G-ring section rings. -/
@[stacks 0HA5]
#check (AlgebraicGeometry.Scheme.gScheme_iff_exists_affineOpenCover :
  ∀ X : Scheme.{u},
    X.GScheme ↔
      ∃ 𝒰 : X.AffineOpenCover, ∀ i : 𝒰.I₀, IsGRing Γ(X, (𝒰.f i).opensRange))

/- Lemma [Stacks 0HA5] (3): a scheme is a G-scheme if and only if some open
cover consists of G-scheme open subschemes. -/
@[stacks 0HA5]
#check (AlgebraicGeometry.Scheme.gScheme_iff_exists_openCover :
  ∀ X : Scheme.{u},
    X.GScheme ↔
      ∃ 𝒰 : X.OpenCover, ∀ i : 𝒰.I₀, Scheme.GScheme ((𝒰.f i).opensRange).toScheme)

/- Lemma [Stacks 0HA5] (4): every open subscheme of a G-scheme is a G-scheme. -/
@[stacks 0HA5]
#check (AlgebraicGeometry.Scheme.gScheme_toScheme :
  ∀ {X : Scheme.{u}} [X.GScheme] (U : X.Opens), Scheme.GScheme U.toScheme)
