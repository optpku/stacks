/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.RingTheory.Regular.GRing

/-!
# Schemes with G-ring stalks

A scheme has G-ring stalks when every structure-sheaf stalk is a G-ring.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme whose structure-sheaf stalks are all G-rings. -/
class HasGRingStalks (S : Scheme.{u}) : Prop where
  /-- Every stalk of the structure sheaf is a G-ring. -/
  isGRing_stalk : ∀ x : S, IsGRing (S.presheaf.stalk x)

attribute [instance] HasGRingStalks.isGRing_stalk

/-- Every stalk of a scheme with G-ring stalks is a G-ring. -/
theorem HasGRingStalks.spec (S : Scheme.{u}) [HasGRingStalks S] (x : S) :
    IsGRing (S.presheaf.stalk x) :=
  sorry

/-- A scheme has G-ring stalks if and only if every structure-sheaf stalk is a
G-ring. -/
theorem hasGRingStalks_iff_forall (S : Scheme.{u}) :
    HasGRingStalks S ↔ ∀ x : S, IsGRing (S.presheaf.stalk x) :=
  sorry

/-- The spectrum of a G-ring has G-ring stalks. -/
instance instHasGRingStalks_of_isGRing {R : Type u} [CommRing R] [IsGRing R] :
    HasGRingStalks (Spec (.of R)) :=
  sorry

end AlgebraicGeometry.Scheme
