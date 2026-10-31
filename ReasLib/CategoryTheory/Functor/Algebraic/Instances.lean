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
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.Over
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
    IsAlgebraicStructure (Type u) (𝟭 (Type u)) := by
  exact {}

/-- The category of pointed sets, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance pointedAlgebraicStructure :
    IsAlgebraicStructure Pointed (forget Pointed) := by
  let F : Pointed ⥤ Under (PUnit : Type _) :=
    { obj := fun X => Under.mk (↾fun _ => X.point)
      map := fun f => Under.homMk (↾f.toFun) (by
        ext x
        exact f.map_point)
      map_id := fun X => Under.UnderMorphism.ext rfl
      map_comp := fun f g => Under.UnderMorphism.ext rfl }
  let G : Under (PUnit : Type _) ⥤ Pointed :=
    { obj := fun X => Pointed.of (X.hom PUnit.unit)
      map := fun f => ⟨f.right, ConcreteCategory.congr_hom (Under.w f) PUnit.unit⟩
      map_id := fun X => Pointed.Hom.ext rfl
      map_comp := fun f g => Pointed.Hom.ext rfl }
  let e : Pointed ≌ Under (PUnit : Type _) := CategoryTheory.Equivalence.mk F G
    (NatIso.ofComponents (fun X => Pointed.Iso.mk (Equiv.refl X) rfl)
      (fun f => Pointed.Hom.ext rfl))
    (NatIso.ofComponents (fun X => Under.isoMk (Iso.refl _) (by
        ext x
        cases x
        rfl))
      (fun f => Under.UnderMorphism.ext rfl))
  letI : F.IsEquivalence := e.isEquivalence_functor
  refine
    { toHasLimitsOfSize := Adjunction.has_limits_of_equivalence F
      toPreservesLimitsOfSize :=
        inferInstanceAs (Limits.PreservesLimitsOfSize (F ⋙ Under.forget _))
      toHasFilteredColimitsOfSize := { HasColimitsOfShape := ?_ }
      toPreservesFilteredColimitsOfSize := { preserves_filtered_colimits := ?_ }
      toReflectsIsomorphisms :=
        inferInstanceAs (F ⋙ Under.forget _).ReflectsIsomorphisms }
  · intro J _ _
    letI : IsConnected J := IsFiltered.isConnected J
    exact Adjunction.hasColimitsOfShape_of_equivalence F
  · intro J _ _
    letI : IsConnected J := IsFiltered.isConnected J
    exact inferInstanceAs (Limits.PreservesColimitsOfShape J (F ⋙ Under.forget _))
/- The explicit equivalence with the coslice under the one-point type identifies the forgetful
functors. The coslice forgetful functor creates limits and connected colimits, and filtered
categories are connected. -/

/-- The category of abelian groups, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance addCommGrpCatAlgebraicStructure :
    IsAlgebraicStructure AddCommGrpCat (forget AddCommGrpCat) := by
  exact {}
/- Proof strategy: apply `IsAlgebraicStructure.mk`; typeclass search supplies limits and their
preservation from `Mathlib.Algebra.Category.Grp.Limits`, filtered colimits and their preservation
from `Mathlib.Algebra.Category.Grp.FilteredColimits`, and reflection of isomorphisms from the
concrete-category API in `Mathlib.Algebra.Category.Grp.Basic`. -/

/-- The category of groups, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance grpCatAlgebraicStructure :
    IsAlgebraicStructure GrpCat (forget GrpCat) := by
  refine { toHasFilteredColimitsOfSize := { HasColimitsOfShape := ?_ } }
  intro J _ _
  exact { has_colimit := fun F =>
    Limits.HasColimit.mk ⟨_, GrpCat.FilteredColimits.colimitCoconeIsColimit F⟩ }
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `GrpCat.hasLimits`,
`GrpCat.forget_preservesLimits`, the filtered-colimit instances in `GrpCat.FilteredColimits`, and
`GrpCat.forget_reflects_isos`, with faithfulness supplied by the canonical concrete-category
forgetful functor. -/

/-- The category of monoids, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance monCatAlgebraicStructure :
    IsAlgebraicStructure MonCat (forget MonCat) := by
  refine { toHasFilteredColimitsOfSize := { HasColimitsOfShape := ?_ } }
  intro J _ _
  exact { has_colimit := fun F =>
    Limits.HasColimit.mk ⟨_, MonCat.FilteredColimits.colimitCoconeIsColimit F⟩ }
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `MonCat.hasLimits`,
`MonCat.forget_preservesLimits`, the filtered-colimit instances in `MonCat.FilteredColimits`, and
`MonCat.forget_reflects_isos`, with faithfulness inherited from the canonical concrete-category
structure. -/

/-- The category of possibly noncommutative rings, with its forgetful functor to sets, is a type
of algebraic structures. -/
instance ringCatAlgebraicStructure :
    IsAlgebraicStructure RingCat (forget RingCat) := by
  refine { toHasFilteredColimitsOfSize := { HasColimitsOfShape := ?_ } }
  intro J _ _
  exact { has_colimit := fun F =>
    Limits.HasColimit.mk ⟨_, RingCat.FilteredColimits.colimitCoconeIsColimit F⟩ }
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `RingCat.hasLimits`,
`RingCat.forget_preservesLimits`, `RingCat.FilteredColimits` and
`RingCat.forget_preservesFilteredColimits`, together with `RingCat.forgetReflectIsos` and the
faithfulness of the canonical forgetful functor. -/

/-- The category of commutative rings, with its forgetful functor to sets, is a type of algebraic
structures. -/
instance commRingCatAlgebraicStructure :
    IsAlgebraicStructure CommRingCat (forget CommRingCat) := by
  refine { toHasFilteredColimitsOfSize := { HasColimitsOfShape := ?_ } }
  intro J _ _
  exact { has_colimit := fun F =>
    Limits.HasColimit.mk ⟨_, CommRingCat.FilteredColimits.colimitCoconeIsColimit F⟩ }
/- Proof strategy: apply `IsAlgebraicStructure.mk`; use `CommRingCat.hasLimits`,
`CommRingCat.forget_preservesLimits`, `CommRingCat.FilteredColimits` and
`CommRingCat.FilteredColimits.forget_preservesFilteredColimits`, together with
`CommRingCat.forgetReflectIsos` and the faithfulness of the canonical forgetful functor. -/

/-- For a possibly noncommutative ring `R`, the category of left `R`-modules with its forgetful
functor to sets is a type of algebraic structures. -/
instance moduleCatAlgebraicStructure (R : Type u) [Ring R] :
    IsAlgebraicStructure (ModuleCat.{v} R) (forget (ModuleCat.{v} R)) := by
  letI : Limits.PreservesColimitsOfSize.{v, v}
      (forget₂ (ModuleCat.{v} R) AddCommGrpCat) :=
    ModuleCat.forget₂PreservesColimitsOfSize.{v, u, v, v} (R := R)
  refine { toPreservesFilteredColimitsOfSize := ?_ }
  exact Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{v} R) AddCommGrpCat) (forget AddCommGrpCat)
/- Forgetting to additive commutative groups preserves all colimits, independently of the scalar
and carrier universes. Composing with the underlying-type functor therefore preserves filtered
colimits. The other properties come from the canonical module-category instances. -/

/-- The commutative-ring specialization, retained for callers of the Stacks 007N examples. -/
theorem moduleCatAlgebraicStructureOfCommRing (R : Type u) [CommRing R] :
    IsAlgebraicStructure (ModuleCat.{v} R) (forget (ModuleCat.{v} R)) :=
  moduleCatAlgebraicStructure R

/-- The category of Lie algebras over a commutative ring is a reusable strengthening of the field
case. -/
instance lieAlgebraCatAlgebraicStructure (R : Type u) [CommRing R] :
    IsAlgebraicStructure (LieAlgebraCat.{v} R) (forget (LieAlgebraCat.{v} R)) := sorry
/- Proof strategy: construct limits as compatible families in the product of the underlying
`R`-modules and construct filtered colimits by descending the pointwise Lie bracket along
`ModuleCat.FilteredColimits`. Show that the forgetful functor preserves both constructions, use
`LieHom.ext` and an inverse linear map to reflect isomorphisms, then apply
`IsAlgebraicStructure.mk`. -/

/-- The field specialization, retained for callers of the Stacks 007N examples. -/
theorem lieAlgebraCatAlgebraicStructureOfField (k : Type u) [Field k] :
    IsAlgebraicStructure (LieAlgebraCat.{v} k) (forget (LieAlgebraCat.{v} k)) :=
  lieAlgebraCatAlgebraicStructure k

