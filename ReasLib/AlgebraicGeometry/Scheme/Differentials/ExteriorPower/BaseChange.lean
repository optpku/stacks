/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.AlgebraSheaf.ExteriorPower.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange

/-!
# Base change of relative differential forms

The canonical comparison from the pullback of relative differential forms to the corresponding
forms after a cartesian base change is an isomorphism in every degree.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials

variable {X' X S' S : Scheme.{u}}
variable {f : X' ⟶ X} {g : S' ⟶ S} {h : X ⟶ S} {h' : X' ⟶ S'}

/-- The map on degree-`p` exterior powers induced by the canonical comparison on relative
differentials attached to a commutative square of schemes. -/
noncomputable def formComparison (sq : CommSq f h' h g) (p : ℕ) :
    (RingedSpace.Hom.pullback f.toShHom).obj (Λ[p] Ω[h.toShHom]) ⟶
      Λ[p] Ω[h'.toShHom] :=
  RingedSpace.ExteriorPower.Pullback.comparison f.toShHom Ω[h.toShHom] p ≫
    RingedSpace.ExteriorPower.map
      (RingedSpace.Hom.Differentials.comparison
        (sq.map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace))) p

/-- The differential-form comparison is the pullback/exterior-power comparison followed by the
exterior power of the relative-differentials comparison. -/
theorem formComparison_eq (sq : CommSq f h' h g) (p : ℕ) :
    formComparison sq p =
      RingedSpace.ExteriorPower.Pullback.comparison f.toShHom Ω[h.toShHom] p ≫
        RingedSpace.ExteriorPower.map
          (RingedSpace.Hom.Differentials.comparison
            (sq.map
              (Scheme.forgetToLocallyRingedSpace ⋙
                LocallyRingedSpace.forgetToSheafedSpace))) p := sorry

/-- For a cartesian square of schemes, the canonical comparison on relative differential forms
is an isomorphism in every degree. -/
instance formComparison_isIso_of_isPullback (hpb : IsPullback f h' h g) (p : ℕ) :
    IsIso (formComparison hpb.toCommSq p) := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials
