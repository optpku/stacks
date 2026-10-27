/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Subfunctor.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Topology.Sets.Closeds

/-!
# Scheme completion along a closed subset

The completion classifies morphisms of schemes over a base whose point-map
image is contained in the specified closed subset.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

namespace completionAlong

/-- A Yoneda section maps into a subset when the underlying scheme morphism
has image contained in that subset. -/
def mapsInto {S : Scheme.{u}} {X : Over S} (T : Set X.left)
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj X).obj U) : Prop :=
  Set.range (x : unop U ⟶ X).left ⊆ T

/-- A section maps into a subset exactly when its point-map range is contained
in that subset. -/
theorem mapsInto_iff {S : Scheme.{u}} {X : Over S} (T : Set X.left)
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj X).obj U) :
    mapsInto T x ↔ Set.range (x : unop U ⟶ X).left ⊆ T :=
  sorry

/-- Image containment is preserved by precomposition over the base scheme. -/
theorem mapsInto_map {S : Scheme.{u}} {X : Over S} {T : Set X.left}
    {U V : (Over S)ᵒᵖ} (φ : U ⟶ V) {x : (yoneda.obj X).obj U}
    (hx : mapsInto T x) :
    mapsInto T ((yoneda.obj X).map φ x) :=
  sorry

/-- The subfunctor of morphisms whose point-map image lies in a closed subset. -/
def subfunctor {S : Scheme.{u}} (X : Over S) (T : Closeds X.left) :
    Subfunctor (yoneda.obj X) where
  obj U := {x : (yoneda.obj X).obj U | mapsInto (T : Set X.left) x}
  map φ _ hx := mapsInto_map φ hx

end completionAlong

/-- The functor of morphisms into a scheme over a base whose point-map image
lies in a specified closed subset. -/
def completionAlong {S : Scheme.{u}} (X : Over S) (T : Closeds X.left) :
    (Over S)ᵒᵖ ⥤ Type u :=
  (completionAlong.subfunctor X T).toFunctor

/-- Completion sections are precisely Yoneda sections mapping into the closed subset. -/
theorem completionAlong_obj {S : Scheme.{u}} (X : Over S) (T : Closeds X.left)
    (U : (Over S)ᵒᵖ) :
    (completionAlong X T).obj U =
      { x : (yoneda.obj X).obj U // completionAlong.mapsInto (T : Set X.left) x } :=
  sorry

namespace completionAlong

/-- The canonical inclusion of the completion into the represented scheme. -/
def ι {S : Scheme.{u}} (X : Over S) (T : Closeds X.left) :
    completionAlong X T ⟶ yoneda.obj X :=
  (subfunctor X T).ι

/-- The inclusion of the completion acts by subtype projection on sections. -/
theorem ι_app {S : Scheme.{u}} (X : Over S) (T : Closeds X.left)
    (U : (Over S)ᵒᵖ) :
    (ι X T).app U = ofHom fun x ↦ x.1 :=
  sorry

/-- A section maps into the closed subset exactly when it lifts to the completion. -/
theorem exists_lift {S : Scheme.{u}} {X : Over S} (T : Closeds X.left)
    {U : (Over S)ᵒᵖ} (x : (yoneda.obj X).obj U) :
    mapsInto (T : Set X.left) x ↔ ∃ y, (ι X T).app U y = x :=
  sorry

end completionAlong

end AlgebraicGeometry.AffineFormalAlgebraicSpace
