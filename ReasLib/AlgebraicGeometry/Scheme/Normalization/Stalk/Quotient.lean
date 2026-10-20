/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stalk.Basic

@[expose] public section

/-!
# Quotients of normalization stalks

This leaf packages the quotient of a normalization pushforward stalk by the
source local ring, together with its length and module-category views.
-/

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Normalization.Stalk

variable (X : Scheme.{u})
variable [QuasiCompact (genericPointSpectrumCoproductTo X)]
variable [QuasiSeparated (genericPointSpectrumCoproductTo X)]

/-- The quotient `(ν_*𝒪_{X^ν})_x / 𝒪_{X,x}`. -/
noncomputable abbrev pushforwardQuotient (x : X) : Type u :=
  pushforward X x ⧸
    (Algebra.linearMap (X.presheaf.stalk x) (pushforward X x)).range

/-- The module length of `(ν_*𝒪_{X^ν})_x / 𝒪_{X,x}` over `𝒪_{X,x}`. -/
noncomputable abbrev pushforwardQuotientLength (x : X) : ℕ∞ :=
  Module.length (X.presheaf.stalk x) (pushforwardQuotient X x)

/-- The quotient `(ν_*𝒪_{X^ν})_x / 𝒪_{X,x}` as an object of the source stalk module category. -/
noncomputable abbrev pushforwardQuotientModule (x : X) :
    ModuleCat.{u} (RingCat.of (X.presheaf.stalk x)) :=
  ModuleCat.of (RingCat.of (X.presheaf.stalk x)) (pushforwardQuotient X x)

end AlgebraicGeometry.Scheme.Normalization.Stalk
