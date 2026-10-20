/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.LocalRingProperty
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.RingTheory.Normal.Locality

/-!
# Locality of normal schemes

This file characterizes normal schemes using affine section rings and open
covers, and records preservation of normality under restriction to opens.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- A scheme is normal exactly when normality of section rings holds locally
on affine neighbourhoods. -/
theorem isNormal_iff_hasRingPropertyLocally :
    X.isNormal ↔
      X.HasRingPropertyLocally (fun R : CommRingCat.{u} ↦ _root_.IsNormalRing R) := sorry

/-- A scheme is normal exactly when the section ring of every affine open is
normal. -/
theorem isNormal_iff_forall_affineOpen :
    X.isNormal ↔
      ∀ U : X.affineOpens, _root_.IsNormalRing (Γ(X, U)) := sorry

/-- A scheme is normal exactly when it has an affine open cover whose section
rings are normal. -/
theorem isNormal_iff_exists_affineOpenCover :
    X.isNormal ↔
      ∃ 𝒰 : X.AffineOpenCover,
        ∀ i : 𝒰.I₀, _root_.IsNormalRing (Γ(X, (𝒰.f i).opensRange)) := sorry

/-- A scheme is normal exactly when it has an open cover by normal open
subschemes. -/
theorem isNormal_iff_exists_openCover :
    X.isNormal ↔
      ∃ 𝒰 : X.OpenCover,
        ∀ i : 𝒰.I₀, ((𝒰.f i).opensRange).toScheme.isNormal := sorry

/-- Every open subscheme of a normal scheme is normal. -/
theorem isNormal_toScheme (hX : X.isNormal) (U : X.Opens) :
    U.toScheme.isNormal := sorry

end AlgebraicGeometry.Scheme
