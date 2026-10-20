/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty
public import ReasLib.RingTheory.LocalProperty.Reduced

/-!
# Reduced schemes

The canonical property remains Mathlib's `IsReduced`. This file supplies
section-ring, stalkwise, affine-neighbourhood, and affine-cover recognition
principles at the scheme layer.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is reduced exactly when every open section ring is reduced. -/
@[stacks 01J1, stacks 01OL]
theorem isReduced_iff :
    IsReduced X ↔ ∀ U : X.Opens, _root_.IsReduced Γ(X, U) := sorry

/-- A scheme is reduced exactly when all of its local rings are reduced. -/
@[stacks 01J1 "stalkwise reducedness criterion"]
theorem isReduced_iff_stalkwise :
    IsReduced X ↔ ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := sorry

/-- Reducedness is the affine-local ring property attached to reduced commutative rings. -/
@[stacks 01OL "locally reducedness criterion"]
theorem isReduced_iff_hasRingPropertyLocally :
    IsReduced X ↔
      X.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ _root_.IsReduced A) := sorry

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.IsReduced

variable (X : Scheme.{u})

/-- A scheme is reduced exactly when one affine open cover has reduced coordinate rings. -/
@[stacks 01OL]
theorem iff_exists_affineOpenCover :
    IsReduced X ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, _root_.IsReduced Γ(X, (𝒰.f i).opensRange) := sorry

/-- A scheme is reduced exactly when every affine open has a reduced coordinate ring. -/
@[stacks 01OL]
theorem iff_forall_affineOpen :
    IsReduced X ↔ ∀ U : X.affineOpens, _root_.IsReduced Γ(X, U) := sorry

/-- Reducedness of a scheme is equivalent to reducedness of the rings of sections on one
affine open cover, on every affine open, and on every open. -/
theorem tfae :
    List.TFAE [
      IsReduced X,
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, _root_.IsReduced Γ(X, (𝒰.f i).opensRange),
      ∀ U : X.affineOpens, _root_.IsReduced Γ(X, U),
      ∀ U : X.Opens, _root_.IsReduced Γ(X, U)] := sorry

end AlgebraicGeometry.IsReduced
