/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Rees
import ReasLib.AlgebraicGeometry.Scheme.Blowup.Pullback
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Pullback.Sum
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Sum.Factors

/-!
# Composition of blowups

Successive blowups in two ideal sheaves compose to a blowup in their product.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Blowup

/-- A blowup in `I`, followed by a blowup in the inverse image of `J`, has composite morphism
satisfying the blowup universal property for `I * J`. -/
theorem compIsBlowup {X : Scheme.{u}} (I J : X.IdealSheafData) (π : Blowup X I)
    (π' : Blowup π.scheme (J.comap π.hom)) :
    IsBlowup (π'.hom ≫ π.hom) (I * J) := sorry

end AlgebraicGeometry.Blowup

namespace AlgebraicGeometry.IsBlowup

/-- For successive blowups in finitely presented closed subschemes `Z` and `Z'`, with
quasi-compact and quasi-separated base `X`, there is a finitely presented closed subscheme
`Y` of `X` whose support is the union of the support of `Z` and the image of the support of
`Z'`, and the composite is the blowup in `Y`. -/
theorem exists_center_comp {X X' X'' : Scheme.{u}}
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (Z : X.IdealSheafData) (hZfp : LocallyOfFinitePresentation Z.subschemeι)
    (b : X' ⟶ X) [IsBlowup b Z]
    (Z' : X'.IdealSheafData) (hZ'fp : LocallyOfFinitePresentation Z'.subschemeι)
    (b' : X'' ⟶ X') [IsBlowup b' Z'] :
    ∃ Y : {Y : X.IdealSheafData // LocallyOfFinitePresentation Y.subschemeι},
      ((Y : X.IdealSheafData).support : Set X) =
          (Z.support : Set X) ∪ b.base '' (Z'.support : Set X') ∧
        IsBlowup (b' ≫ b) (Y : X.IdealSheafData) := sorry

end AlgebraicGeometry.IsBlowup

namespace AlgebraicGeometry.IsAdmissibleBlowup

/-- The composite of a blowup admissible over `U` and a blowup admissible over the inverse
image of `U` is again admissible over `U`. -/
theorem comp {X X' X'' : Scheme.{u}}
    [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
    (U : X.Opens) (hU : QuasiCompact U.ι)
    (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b)
    (b' : X'' ⟶ X') (hb' : IsAdmissibleBlowup (b ⁻¹ᵁ U) b') :
    IsAdmissibleBlowup U (b' ≫ b) := sorry

end AlgebraicGeometry.IsAdmissibleBlowup
