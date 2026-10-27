/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.MonCat.FilteredColimits
public import Mathlib.Algebra.Category.MonCat.Limits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Category.Pointed
public import ReasLib.Algebra.Category.LieAlgebraCat.Basic
public import ReasLib.CategoryTheory.Functor.Algebraic.Basic

/-!
# Standard categories of algebraic structures

This file supplies `IsAlgebraicStructure` instances for the standard bundled algebraic
categories. The bundled categories and their forgetful functors remain the canonical data owners.
-/

@[expose] public section

open CategoryTheory

universe v u

/- The module and Lie-algebra instances allow an independent carrier universe `v`. The ring and
module statements cover noncommutative bases where mathlib's canonical bundled categories do. -/

/-- The category of types, with its identity functor, satisfies the algebraic-structure interface.
This gives set-valued constructions the same generic coefficient-change API as bundled algebraic
categories. -/
instance typeAlgebraicStructure :
    IsAlgebraicStructure (Type u) (𝟭 (Type u)) := sorry

/-- The category of pointed sets, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance pointedAlgebraicStructure :
    IsAlgebraicStructure Pointed (forget Pointed) := sorry
/- Proof strategy: identify `Pointed` with the coslice category under the one-point type. Use
`CategoryTheory.Limits.Under.hasLimits`, the corresponding colimit instances, and
`typeToPointedForgetAdjunction` for preservation of limits; filtered colimits are created by the
underlying-type functor, and `Pointed.Iso.mk` turns a bijective underlying map into an isomorphism. -/

/-- The category of abelian groups, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance addCommGrpCatAlgebraicStructure :
    IsAlgebraicStructure AddCommGrpCat (forget AddCommGrpCat) := sorry
/- Proof strategy: apply `IsAlgebraicStructure.mk`; typeclass search supplies limits and their
preservation from `Mathlib.Algebra.Category.Grp.Limits`, filtered colimits and their preservation
from `Mathlib.Algebra.Category.Grp.FilteredColimits`, and reflection of isomorphisms from the
concrete-category API in `Mathlib.Algebra.Category.Grp.Basic`. -/

/-- The category of groups, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance grpCatAlgebraicStructure :
    IsAlgebraicStructure GrpCat (forget GrpCat) := sorry
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `GrpCat.hasLimits`,
`GrpCat.forget_preservesLimits`, the filtered-colimit instances in `GrpCat.FilteredColimits`, and
`GrpCat.forget_reflects_isos`, with faithfulness supplied by the canonical concrete-category
forgetful functor. -/

/-- The category of monoids, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance monCatAlgebraicStructure :
    IsAlgebraicStructure MonCat (forget MonCat) := sorry
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `MonCat.hasLimits`,
`MonCat.forget_preservesLimits`, the filtered-colimit instances in `MonCat.FilteredColimits`, and
`MonCat.forget_reflects_isos`, with faithfulness inherited from the canonical concrete-category
structure. -/

/-- The category of possibly noncommutative rings, with its forgetful functor to sets, is a type
of algebraic structures. -/
instance ringCatAlgebraicStructure :
    IsAlgebraicStructure RingCat (forget RingCat) := sorry
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `RingCat.hasLimits`,
`RingCat.forget_preservesLimits`, `RingCat.FilteredColimits` and
`RingCat.forget_preservesFilteredColimits`, together with `RingCat.forgetReflectIsos` and the
faithfulness of the canonical forgetful functor. -/

/-- The category of commutative rings, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance commRingCatAlgebraicStructure :
    IsAlgebraicStructure CommRingCat (forget CommRingCat) := sorry
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `CommRingCat.hasLimits`,
`CommRingCat.forget_preservesLimits`, `CommRingCat.FilteredColimits` and
`CommRingCat.FilteredColimits.forget_preservesFilteredColimits`, together with
`CommRingCat.forgetReflectIsos` and the faithfulness of the canonical forgetful functor. -/

/-- For a possibly noncommutative ring `R`, the category of left `R`-modules with its forgetful
functor to sets is a type of algebraic structures. -/
instance moduleCatAlgebraicStructure (R : Type u) [Ring R] :
    IsAlgebraicStructure (ModuleCat.{v} R) (forget (ModuleCat.{v} R)) := sorry
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `ModuleCat.hasLimits`,
`ModuleCat.forget_preservesLimits`, and
`ModuleCat.FilteredColimits.forget_preservesFilteredColimits`. The canonical `ConcreteCategory`
instance supplies faithfulness, while `Mathlib.Algebra.Category.ModuleCat.Basic` supplies
reflection of isomorphisms. -/

/-- The category of Lie algebras over a commutative ring is a reusable strengthening of the field
case. -/
instance lieAlgebraCatAlgebraicStructure (R : Type u) [CommRing R] :
    IsAlgebraicStructure (LieAlgebraCat.{v} R) (forget (LieAlgebraCat.{v} R)) := sorry
/- Proof strategy: construct limits as compatible families in the product of the underlying
`R`-modules and construct filtered colimits by descending the pointwise Lie bracket along
`ModuleCat.FilteredColimits`. Show that the forgetful functor preserves both constructions, use
`LieHom.ext` and an inverse linear map to reflect isomorphisms, then apply
`IsAlgebraicStructure.mk`. -/

