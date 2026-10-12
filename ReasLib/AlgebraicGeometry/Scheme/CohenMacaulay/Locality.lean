/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty.Locality
public import ReasLib.RingTheory.CohenMacaulay.Local

/-!
# Locality of Cohen-Macaulay schemes

This file characterizes Cohen-Macaulay schemes by the Cohen-Macaulayness of
the section rings of all affine open subschemes.
-/

@[expose] public section

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is Cohen-Macaulay exactly when every affine open has a Cohen-Macaulay
ring of sections. -/
theorem cohenMacaulay_iff_forall_affineOpen_sectionsRing_cohenMacaulayRing :
    CohenMacaulay X ↔
      ∀ U : X.affineOpens, CohenMacaulayRing (Γ(X, U)) := sorry

end AlgebraicGeometry.Scheme
