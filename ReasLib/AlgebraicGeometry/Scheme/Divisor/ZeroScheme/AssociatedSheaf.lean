/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.ZeroScheme

/-!
# The zero scheme of the canonical section of a Cartier divisor

This file identifies an effective Cartier divisor with the zero scheme of the canonical
section of its associated invertible sheaf.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The zero scheme of the canonical section of `D.associatedSheaf` is canonically
isomorphic to the divisor subscheme of `D`. -/
noncomputable def associatedZeroSchemeIso {X : Scheme.{u}} (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    Scheme.zeroScheme D.associatedSheaf D.canonicalSection ≅ D.subscheme :=
  eqToIso (congrArg IdealSheafData.subscheme
    (zeroIdealSheaf_associatedSheaf_canonicalSection D))

/-- The canonical zero-scheme isomorphism respects the closed immersions into `X`. -/
theorem associatedZeroSchemeIso_hom_subschemeι {X : Scheme.{u}}
    (D : X.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    (D.associatedZeroSchemeIso).hom ≫ D.subschemeι =
      Scheme.zeroSchemeι D.associatedSheaf D.canonicalSection := sorry

/-- The canonical zero-scheme isomorphism respects the structure morphism to the base. -/
theorem associatedZeroSchemeIso_hom_comp {S : Scheme.{u}} {X : Over S}
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    (D.associatedZeroSchemeIso).hom ≫ (D.subschemeι ≫ X.hom) =
      Scheme.zeroSchemeι D.associatedSheaf D.canonicalSection ≫ X.hom := sorry

/-- The canonical identification of the zero scheme of `D.canonicalSection` with `D`,
regarded over the same base. -/
noncomputable def associatedZeroSchemeOverIso {S : Scheme.{u}} {X : Over S}
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    Over.mk (Scheme.zeroSchemeι D.associatedSheaf D.canonicalSection ≫ X.hom) ≅
      Over.mk (D.subschemeι ≫ X.hom) :=
  Over.isoMk D.associatedZeroSchemeIso (associatedZeroSchemeIso_hom_comp D)

/-- The underlying map of the over-category identification is the canonical scheme
isomorphism. -/
theorem associatedZeroSchemeOverIso_hom_left {S : Scheme.{u}} {X : Over S}
    (D : X.left.IdealSheafData) [IsEffectiveCartierDivisor D.subschemeι] :
    (D.associatedZeroSchemeOverIso).hom.left = D.associatedZeroSchemeIso.hom := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
