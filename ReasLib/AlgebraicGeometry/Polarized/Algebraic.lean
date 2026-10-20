/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.Polarized.ToSpaces

/-!
# Algebraicity of the polarized forgetful functor

The fibres of the forgetful functor from polarized proper schemes to
finite-presentation flat proper algebraic-space families are modelled by
costructured-arrow categories and form algebraic stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Spaces hiding p
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Polarized

/-- The projection of the Yoneda 2-fibre product of `toFpFlatProper` against an
object `ξ` of `Spaces'_{fp, flat, proper}`, sending a costructured arrow to the
base scheme of its Polarized source, viewed in `Over (⊤_ Scheme)`. -/
def twoFibreProduct.p (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    CostructuredArrow toFpFlatProper ξ ⥤ Over (⊤_ Scheme.{u}) :=
  CostructuredArrow.proj toFpFlatProper ξ ⋙ Polarized.p ⋙ asOverTerminal

/-- The projection `twoFibreProduct.p ξ` is the costructured-arrow projection of
`toFpFlatProper`, followed by the Polarized base-scheme functor and the
identification of schemes with objects of `Over (⊤_ Scheme)`. -/
theorem twoFibreProduct.p_eq (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    twoFibreProduct.p ξ =
      CostructuredArrow.proj toFpFlatProper ξ ⋙ Polarized.p ⋙ asOverTerminal :=
  sorry

/-- The Yoneda 2-fibre product projection of `toFpFlatProper` against an object
of `Spaces'_{fp, flat, proper}` is fibred in groupoids. -/
instance instIsFiberedInGroupoids_twoFibreProduct
    (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    Functor.IsFibered.InGroupoids (twoFibreProduct.p ξ) :=
  sorry

/-- The Yoneda 2-fibre product `(Sch/T)_fppf ×_{ξ, Spaces'_{fp, flat, proper}} Polarized`,
as a category fibred in groupoids over `Over (⊤_ Scheme)`. Here `T` is the base
scheme of `ξ`. -/
def twoFibreProduct (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    GroupoidsOver (⊤_ Scheme.{u}) :=
  FiberedCategoryOver.Groupoids.ofFunctor.{u + 1, u, u + 1, u}
    (twoFibreProduct.p ξ)

/-- The projection of `twoFibreProduct ξ` is `twoFibreProduct.p ξ`. -/
theorem twoFibreProduct_p (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    (twoFibreProduct ξ).p = twoFibreProduct.p ξ :=
  sorry

/-- The total category of `twoFibreProduct ξ` is the costructured-arrow category
of `toFpFlatProper` over `ξ`. -/
theorem twoFibreProduct_total (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    (twoFibreProduct ξ).total = CostructuredArrow toFpFlatProper ξ :=
  sorry

/-- The Yoneda fibre of the forgetful functor from polarized proper schemes to
finite-presentation flat proper algebraic-space families is an algebraic stack. -/
@[stacks 0D41]
instance instAlgebraicStack_twoFibreProduct
    (ξ : FpFlatProperGroupoids (⊤_ Scheme.{u})) :
    AlgebraicStack (twoFibreProduct ξ) :=
  sorry

end AlgebraicGeometry.Polarized
