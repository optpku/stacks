/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Square
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Composition.BoundedBelow.Exact
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Exact.Bounded.RightDerived
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.RightDerived.Naturality
import Mathlib.Tactic.CrossRefAttribute

/-!
# Bounded-below right-derived squares with exact horizontal functors

This leaf packages the common situation in which the second functor on the source side and the
first functor on the target side are exact.  Their direct actions on `D⁺` are used in the public
source and target, while comparison with canonical right-derived functors remains explicit.

The data-clean constructor `mapOfIso` accepts a concrete source comparison isomorphism.  The
convenience constructor `map` instead accepts an explicit proof that the canonical source
comparison is invertible; no local or global instance is installed merely to select its inverse.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w vA vB vC vD uA uB uC uD

namespace CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact

-- Independent derived-category universe levels make elaboration substantially more expensive
-- for the comparison maps below; keep the public API heterogeneous while allowing this file's
-- definitional reductions to finish.
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]

variable {F : A ⥤ B} {G : B ⥤ₑ C} {I : A ⥤ₑ D} {H : D ⥤ C}
  [F.Additive] [H.Additive]

variable [F.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [H.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso D)]
variable [(F ⋙ G.obj).toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [(I.obj ⋙ H).toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]
variable [G.obj.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso B)]
variable [I.obj.toBoundedBelowDerived.HasRightDerivedFunctor
  (HomotopyCategory.Plus.quasiIso A)]

/-- The two-stage source `RF ⋙ DG`, where the second functor acts directly because it is
exact. -/
@[stacks 015M "bounded-below exact-horizontal square source"]
abbrev source (F : A ⥤ B) (G : B ⥤ₑ C) [F.Additive]
    [F.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso A)] :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus C :=
  Functor.RightDerived.Bounded.functor F ⋙ ExactFunctor.Derived.Plus.functor G

/-- The two-stage target `DI ⋙ RH`, where the first functor acts directly because it is
exact. -/
@[stacks 015M "bounded-below exact-horizontal square target"]
abbrev target (I : A ⥤ₑ D) (H : D ⥤ C) [H.Additive]
    [H.toBoundedBelowDerived.HasRightDerivedFunctor
      (HomotopyCategory.Plus.quasiIso D)] :
    DerivedCategory.Plus A ⥤ DerivedCategory.Plus C :=
  ExactFunctor.Derived.Plus.functor I ⋙ Functor.RightDerived.Bounded.functor H

/-- The canonical comparison from the one-stage right-derived source to `RF ⋙ DG`. -/
@[stacks 015M "bounded-below exact-horizontal source comparison"]
noncomputable def sourceComparison :
    Functor.RightDerived.Bounded.functor (F ⋙ G.obj) ⟶ source F G :=
  Functor.RightDerived.Composition.BoundedBelow.comparison F G.obj ≫
    Functor.whiskerLeft (Functor.RightDerived.Bounded.functor F)
      (ExactFunctor.Derived.Plus.rightDerivedComparison G)

/-- The canonical comparison from the one-stage right-derived target to `DI ⋙ RH`. -/
@[stacks 015M "bounded-below exact-horizontal target comparison"]
noncomputable def targetComparison :
    Functor.RightDerived.Bounded.functor (I.obj ⋙ H) ⟶ target I H :=
  Functor.RightDerived.Composition.BoundedBelow.comparison I.obj H ≫
    Functor.whiskerRight (ExactFunctor.Derived.Plus.rightDerivedComparison I)
      (Functor.RightDerived.Bounded.functor H)

/-- The source comparison with its inverse constructed from the exact second functor. -/
@[stacks 015M "bounded-below exact-horizontal source comparison isomorphism"]
noncomputable def sourceIso [EnoughInjectives A] [EnoughInjectives B] :
    Functor.RightDerived.Bounded.functor (F ⋙ G.obj) ≅ source F G :=
  asIso (Functor.RightDerived.Composition.BoundedBelow.comparison F G.obj) ≪≫
    Functor.isoWhiskerLeft (Functor.RightDerived.Bounded.functor F)
      (ExactFunctor.Derived.Plus.rightDerivedIso G)

/-- The explicit source isomorphism has the canonical source comparison as its forward map. -/
@[simp]
theorem sourceIso_hom [EnoughInjectives A] [EnoughInjectives B] :
    (sourceIso (F := F) (G := G)).hom = sourceComparison (F := F) (G := G) := rfl

/-- Exactness of the second functor makes the canonical source comparison invertible. -/
@[stacks 015M "bounded-below exact-horizontal source comparison is invertible"]
theorem sourceComparison_isIso [EnoughInjectives A] [EnoughInjectives B] :
    IsIso (sourceComparison (F := F) (G := G)) :=
  (sourceIso (F := F) (G := G)).isIso_hom

/-- The exact-horizontal square map built from a concrete source comparison isomorphism. -/
@[stacks 015M "bounded-below exact-horizontal square map from an isomorphism"]
noncomputable def mapOfIso
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G.obj) ≅ source F G) :
    source F G ⟶ target I H :=
  e.inv ≫ Functor.RightDerived.Bounded.map τ ≫ targetComparison

/-- The exact-horizontal square map obtained from an explicit invertibility certificate for the
canonical source comparison. -/
@[stacks 015M "bounded-below exact-horizontal square map"]
noncomputable def map
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (h : IsIso (sourceComparison (F := F) (G := G))) :
    source F G ⟶ target I H :=
  mapOfIso τ (@asIso _ _ _ _ (sourceComparison (F := F) (G := G)) h)

/-- Specification of an exact-horizontal square map relative to a concrete source comparison
isomorphism. -/
@[stacks 015M "bounded-below exact-horizontal square specification from an isomorphism"]
def IsMapOfIso
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G.obj) ≅ source F G)
    (η : source F G ⟶ target I H) : Prop :=
  e.hom ≫ η = Functor.RightDerived.Bounded.map τ ≫ targetComparison

/-- Specification using the canonical exact-horizontal source comparison. -/
@[stacks 015M "bounded-below exact-horizontal square specification"]
def IsMap (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (η : source F G ⟶ target I H) : Prop :=
  sourceComparison ≫ η = Functor.RightDerived.Bounded.map τ ≫ targetComparison

/-- Objectwise form of the canonical exact-horizontal square specification. -/
@[stacks 015M "bounded-below exact-horizontal component specification"]
def IsMapAt (τ : F ⋙ G.obj ⟶ I.obj ⋙ H) (K : DerivedCategory.Plus A)
    (η : (source F G).obj K ⟶ (target I H).obj K) : Prop :=
  sourceComparison.app K ≫ η =
    (Functor.RightDerived.Bounded.map τ).app K ≫ targetComparison.app K

/-- The map built from a concrete source isomorphism satisfies its defining equation. -/
@[stacks 015M "bounded-below exact-horizontal map-from-iso specification"]
theorem mapOfIso_isMapOfIso
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G.obj) ≅ source F G) :
    IsMapOfIso τ e (mapOfIso τ e) := sorry

/-- The canonical exact-horizontal map satisfies its defining equation. -/
@[stacks 015M "bounded-below exact-horizontal map specification"]
theorem map_isMap
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (h : IsIso (sourceComparison (F := F) (G := G))) :
    IsMap τ (map τ h) := sorry

/- The comparison data are kept explicit: invertibility of the source and target comparison
maps is a hypothesis of this bridge, not an ambient instance synthesized by the library. -/
/-- If the underived square map and the target comparison are invertible, the exact-horizontal
bounded-below derived square map is invertible as well. -/
@[stacks 015M "bounded-below exact-horizontal square isomorphism transport"]
theorem map_isIso
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (h : IsIso (sourceComparison (F := F) (G := G)))
    [IsIso τ]
    [IsIso (targetComparison (I := I) (H := H))] :
    IsIso (map τ h) := sorry

/-- Every component of the canonical exact-horizontal map satisfies the objectwise equation. -/
@[stacks 015M "bounded-below exact-horizontal component specification"]
theorem map_isMapAt
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (h : IsIso (sourceComparison (F := F) (G := G)))
    (K : DerivedCategory.Plus A) :
    IsMapAt τ K ((map τ h).app K) := sorry

/-- The concrete-source-iso specification determines the exact-horizontal map uniquely. -/
@[stacks 015M "uniqueness of exact-horizontal maps from an isomorphism"]
theorem IsMapOfIso.eq_mapOfIso
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (e : Functor.RightDerived.Bounded.functor (F ⋙ G.obj) ≅ source F G)
    {η : source F G ⟶ target I H}
    (hη : IsMapOfIso τ e η) :
    η = mapOfIso τ e := sorry

/-- The canonical comparison equation determines the exact-horizontal square map uniquely. -/
@[stacks 015M "uniqueness of exact-horizontal square maps"]
theorem IsMap.eq_map
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (h : IsIso (sourceComparison (F := F) (G := G)))
    {η : source F G ⟶ target I H}
    (hη : IsMap τ η) :
    η = map τ h := sorry

/-- The objectwise comparison equation determines the corresponding component uniquely. -/
@[stacks 015M "uniqueness of exact-horizontal square components"]
theorem IsMapAt.eq_app
    (τ : F ⋙ G.obj ⟶ I.obj ⋙ H)
    (h : IsIso (sourceComparison (F := F) (G := G)))
    (K : DerivedCategory.Plus A)
    {η : (source F G).obj K ⟶ (target I H).obj K}
    (hη : IsMapAt τ K η) :
    η = (map τ h).app K := sorry

end CategoryTheory.Functor.RightDerived.Composition.BoundedBelow.Square.Exact
