/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Restriction of curve families to open subschemes of their bases
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/-- The open `U` of the base of a family of curves, as a scheme over `S`. -/
def baseOpen {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) : Over S :=
  Over.mk (U.ι ≫ (base P).hom)

/-- The structure morphism of `baseOpen P U` is `U.ι ≫ (base P).hom`. -/
theorem baseOpen_hom {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    (baseOpen P U).hom = U.ι ≫ (base P).hom := sorry

/-- The open immersion of `U` as a morphism of bases over `S`. -/
def baseOpenι {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    baseOpen P U ⟶ base P :=
  Over.homMk U.ι

/-- The underlying scheme morphism of `baseOpenι P U` is `U.ι`. -/
theorem baseOpenι_left {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    (baseOpenι P U).left = U.ι := sorry

/-- Base change of an fp-flat-proper family of curves along an open of the base
remains fp-flat-proper. -/
theorem fpFlatProper_pullback_snd_baseOpenι {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens) :
    FpFlatProper (pullback.snd (hom P) (ofOverMap (baseOpenι P U))) := sorry

/-- Base change of a family of curves of relative dimension at most `1` along an
open of the base remains of relative dimension at most `1`. -/
theorem relativeDimensionLE_pullback_snd_baseOpenι {S : Scheme.{u}}
    (P : Obj S) (U : (base P).left.Opens) :
    RelativeDimensionLE (pullback.snd (hom P) (ofOverMap (baseOpenι P U))) 1 := sorry

/-- The base change of a family of curves to an open of its base. -/
def baseChangeToOpen {S : Scheme.{u}} (P : Obj S) (U : (base P).left.Opens) :
    Obj S :=
  @mk _ _ _ (pullback.snd (hom P) (ofOverMap (baseOpenι P U)))
    (fpFlatProper_pullback_snd_baseOpenι P U)
    (relativeDimensionLE_pullback_snd_baseOpenι P U)

/-- The structure morphism of `baseChangeToOpen P U` is the second projection of
the pullback of `hom P` along `ofOverMap (baseOpenι P U)`. -/
theorem baseChangeToOpen_hom {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens) :
    hom (baseChangeToOpen P U) =
      pullback.snd (hom P) (ofOverMap (baseOpenι P U)) := sorry

/-- The base of `baseChangeToOpen P U` is `baseOpen P U`. -/
theorem baseChangeToOpen_base {S : Scheme.{u}} (P : Obj S)
    (U : (base P).left.Opens) :
    base (baseChangeToOpen P U) = baseOpen P U := sorry

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
