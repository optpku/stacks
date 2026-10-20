/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale.FiniteFibers

/-!
# Property (α) for algebraic spaces

An algebraic space has property (α) when every affine étale scheme chart has
finite fibre over every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space has property (α) if every étale morphism from an affine
scheme has finite fibre over every point. -/
@[mk_iff]
class HasPropertyAlpha {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Affine étale morphisms from schemes into `X` have finite fibre over every
  point of `|X|`. -/
  finiteFibre : ∀ x : Points X, forallAffineEtaleFiniteFibre X x

namespace HasPropertyAlpha

/-- An algebraic space with property (α) has finite affine étale fibres over
every point. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [HasPropertyAlpha X] :
    ∀ x : Points X, forallAffineEtaleFiniteFibre X x :=
  HasPropertyAlpha.finiteFibre

/-- The affine étale finite-fibre test at every point witnesses property (α). -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ x : Points X, forallAffineEtaleFiniteFibre X x) :
    HasPropertyAlpha X :=
  ⟨h⟩

end HasPropertyAlpha

/-- A scheme over `S`, viewed as an algebraic space, has property (α). -/
instance instHasPropertyAlpha_ofOver {S : Scheme.{u}} (T : Over S) :
    HasPropertyAlpha (ofOver T) :=
  sorry

/-- Property (α) is equivalent to existence of an étale scheme covering with
finite fibres over every point. -/
theorem hasPropertyAlpha_iff_existsEtaleCoverFiniteFibre {S : Scheme.{u}}
    (X : AlgebraicSpace S) :
    HasPropertyAlpha X ↔ ∀ x : Points X, existsEtaleCoverFiniteFibre X x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
