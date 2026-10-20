/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.Equivalence
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bicategorical packaging of based equivalences

This module relates same-universe `BasedFunctor.IsEquivalence` data to canonical bicategorical
equivalences in `Cat/C`.
-/

@[expose] public section

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open BasedNatTrans
open Bicategory
open scoped Bicategory

universe u v uS uX uY vS vX vY

variable {C : Type u} [Category.{v} C]

namespace BasedFunctor

variable {X : BasedCategory.{vX, uX} C} {Y : BasedCategory.{vY, uY} C}

section SameUniverse

variable {X : BasedCategory.{vS, uS} C} {Y : BasedCategory.{vS, uS} C}

namespace QuasiInverse

variable {F : X ⥤ᵇ Y}

/-- In the same-universe case, explicit equivalence-over-base data package into the canonical
bicategorical equivalence object in `Cat/C`. -/
noncomputable def toEquivalence (e : QuasiInverse F) : X ≌ Y :=
  Bicategory.Equivalence.mkOfAdjointifyUnit e.unitIso e.counitIso

/-- Package explicit based quasi-inverse data as a bicategorical equivalence while retaining the
supplied unit. The counit is canonically adjusted by `Bicategory.adjointifyCounit`.

Use this variant when subsequent calculations are expressed in terms of the chosen unit. The
default `QuasiInverse.toEquivalence` instead retains the chosen counit, which is the more useful
orientation for the project's fibered-category equivalence API. -/
noncomputable def toEquivalencePreservingUnit (e : QuasiInverse F) : X ≌ Y :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.unitIso e.counitIso

/-- The forward morphism of the bicategorical equivalence built from `e` is the original based
functor. -/
@[simp] theorem toEquivalence.hom (e : QuasiInverse F) :
    e.toEquivalence.hom = F := sorry
/- Proof strategy: unfold `toEquivalence`; the hom projection of
`Bicategory.Equivalence.mkOfAdjointifyUnit` is definitionally the supplied functor `F`. -/

/-- The inverse morphism of the bicategorical equivalence built from `e` is the chosen based
quasi-inverse. -/
@[simp] theorem toEquivalence.inv (e : QuasiInverse F) :
    e.toEquivalence.inv = e.inverse := sorry
/- Proof strategy: unfold `toEquivalence`; its inverse projection is definitionally
the `QuasiInverse.inverse` supplied to `mkOfAdjointifyUnit`. -/

/-- The unit of the packaged bicategorical equivalence is the canonical adjustment of the
supplied unit against the supplied counit. -/
theorem toEquivalence.unit (e : QuasiInverse F) :
    e.toEquivalence.unit =
      Bicategory.Equivalence.adjointifyUnit e.unitIso e.counitIso := sorry

/-- Packaging explicit based quasi-inverse data retains the supplied counit isomorphism. -/
@[simp]
theorem toEquivalence.counit (e : QuasiInverse F) :
    e.toEquivalence.counit = e.counitIso := sorry

/-- The forward morphism of the unit-preserving bicategorical equivalence is the original based
functor. -/
@[simp]
theorem toEquivalencePreservingUnit.hom (e : QuasiInverse F) :
    e.toEquivalencePreservingUnit.hom = F := sorry

/-- The inverse morphism of the unit-preserving bicategorical equivalence is the supplied based
quasi-inverse. -/
@[simp]
theorem toEquivalencePreservingUnit.inv (e : QuasiInverse F) :
    e.toEquivalencePreservingUnit.inv = e.inverse := sorry

/-- The unit of the unit-preserving bicategorical equivalence is the supplied unit candidate. -/
@[simp]
theorem toEquivalencePreservingUnit.unit (e : QuasiInverse F) :
    e.toEquivalencePreservingUnit.unit = e.unitIso := sorry

/-- The counit of the unit-preserving bicategorical equivalence is the canonical adjustment of
the supplied counit against the supplied unit. -/
@[simp]
theorem toEquivalencePreservingUnit.counit (e : QuasiInverse F) :
    e.toEquivalencePreservingUnit.counit =
      Bicategory.adjointifyCounit e.unitIso e.counitIso := sorry

end QuasiInverse

/-- Interpret a same-owner based functor satisfying `IsEquivalence` as a bicategorical
equivalence. This is the based analogue of `Functor.asEquivalence`. -/
noncomputable def asEquivalence (F : X ⥤ᵇ Y) [F.IsEquivalence] : X ≌ Y :=
  F.asQuasiInverse.toEquivalence

/-- Package an explicit proof that a based functor is an equivalence over the base as a
bicategorical equivalence.

Unlike `asEquivalence`, this bridge takes the proposition as ordinary data. It avoids a local
instance when independent criteria establish the equivalence, while reusing
`BasedFunctor.asQuasiInverse` as the unique choice boundary. -/
noncomputable def asEquivalenceOf (F : X ⥤ᵇ Y) (h : F.IsEquivalence) : X ≌ Y :=
  (F.asQuasiInverseOf h).toEquivalence

/-- The forward `1`-morphism of `BasedFunctor.asEquivalence F` is `F`. -/
@[simp]
theorem asEquivalence.hom (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.asEquivalence.hom = F := sorry
/- Proof strategy: unfold `BasedFunctor.asEquivalence` and apply
`QuasiInverse.toEquivalence.hom`. -/

/-- The forward `1`-morphism of an equivalence packaged from an explicit proof is the original
based functor. -/
@[simp]
theorem asEquivalenceOf.hom (F : X ⥤ᵇ Y) (h : F.IsEquivalence) :
    (F.asEquivalenceOf h).hom = F := sorry

/-- The inverse `1`-morphism of an equivalence packaged from an explicit proof is the inverse in
the quasi-inverse data selected through that proof. -/
@[simp]
theorem asEquivalenceOf.inv (F : X ⥤ᵇ Y) (h : F.IsEquivalence) :
    (F.asEquivalenceOf h).inv = (F.asQuasiInverseOf h).inverse := sorry

/-- The unit of an equivalence packaged from an explicit proof is the canonical adjustment of
the unit and counit selected through that proof. -/
theorem asEquivalenceOf.unit (F : X ⥤ᵇ Y) (h : F.IsEquivalence) :
    (F.asEquivalenceOf h).unit =
      Bicategory.Equivalence.adjointifyUnit
        (F.asQuasiInverseOf h).unitIso (F.asQuasiInverseOf h).counitIso := sorry

/-- The counit of an equivalence packaged from an explicit proof is the counit selected through
that proof. -/
@[simp]
theorem asEquivalenceOf.counit (F : X ⥤ᵇ Y) (h : F.IsEquivalence) :
    (F.asEquivalenceOf h).counit = (F.asQuasiInverseOf h).counitIso := sorry

/-- The inverse `1`-morphism selected by `BasedFunctor.asEquivalence F` is the chosen based
inverse `F.inv`. -/
@[simp]
theorem asEquivalence.inv (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.asEquivalence.inv = F.inv := sorry
/- Proof strategy: unfold `BasedFunctor.asEquivalence`, `BasedFunctor.inv`, and use
`QuasiInverse.toEquivalence.inv`. -/

/-- The unit of `BasedFunctor.asEquivalence F` is the canonical adjustment of the named chosen
unit against the named chosen counit over the base. -/
theorem asEquivalence.unit (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.asEquivalence.unit =
      Bicategory.Equivalence.adjointifyUnit F.unitIso F.counitIso := sorry

/-- The counit of `BasedFunctor.asEquivalence F` is the named chosen counit over the base. -/
@[simp]
theorem asEquivalence.counit (F : X ⥤ᵇ Y) [F.IsEquivalence] :
    F.asEquivalence.counit = F.counitIso := sorry

/-- The forward `1`-morphism of a bicategorical equivalence is an equivalence over the base. -/
theorem hom.isEquivalence (e : X ≌ Y) :
    e.hom.IsEquivalence := sorry
/- Proof strategy: apply `IsEquivalence.mk'` to `e.inv`, with the canonical unit and
counit isomorphisms carried by the bicategorical equivalence `e`. -/

/-- In one fixed based-category bicategory, `F.IsEquivalence` is equivalent to occurrence as the
forward morphism of a bicategorical equivalence. -/
theorem isEquivalence_iff_exists_equivalence (F : X ⥤ᵇ Y) :
    F.IsEquivalence ↔ ∃ e : X ≌ Y, e.hom = F := sorry
/- Proof strategy: install the forward hypothesis as an instance and use `F.asEquivalence`; in
the reverse direction use `hom.isEquivalence`. -/

/-- Typeclass bridge from a bicategorical equivalence to the property carried by its forward
`1`-morphism. -/
instance homIsEquivalence (e : X ≌ Y) :
    e.hom.IsEquivalence := sorry

/-- Typeclass bridge from a bicategorical equivalence to the property carried by its inverse
`1`-morphism. -/
instance invIsEquivalence (e : X ≌ Y) :
    e.inv.IsEquivalence := sorry

end SameUniverse

end BasedFunctor

end CategoryTheory
