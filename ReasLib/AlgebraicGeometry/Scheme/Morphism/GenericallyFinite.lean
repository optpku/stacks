/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite.GenericFiber

/-!
# Generically finite morphisms

This file records two useful generically finite conditions for morphisms of schemes: finiteness of
the fibers over generic points of the target and local quasi-finiteness over a dense open of the
source. Under standard finiteness hypotheses, the source condition implies the target condition.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism is generically finite on the target when every fiber over a generic point of the
target is finite. -/
class GenericallyFiniteOnTarget {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- Every generic point of the target has finite inverse image. -/
  finiteGenericFiber :
    ∀ η : Y, η ∈ genericPoints Y →
      ({x : X | f.base x = η} : Set X).Finite

/-- A morphism is generically finite on the target exactly when every fiber over a generic point
of the target is finite. -/
theorem genericallyFiniteOnTarget_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.GenericallyFiniteOnTarget ↔
      ∀ η : Y, η ∈ genericPoints Y →
        ({x : X | f.base x = η} : Set X).Finite := sorry

/-- For a morphism generically finite on the target, the fiber over each generic point is finite
as a subtype. -/
instance instFiniteGenericFiberSubtypeOfGenericallyFiniteOnTarget
    {X Y : Scheme.{u}} (f : X ⟶ Y) [f.GenericallyFiniteOnTarget]
    (η : Y) [Fact (η ∈ genericPoints Y)] :
    Finite {x : X // f.base x = η} := sorry

/-- A morphism is generically finite on the source when it is locally quasi-finite on some dense
open subscheme of its source. -/
class GenericallyFiniteOnSource {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  /-- There is a dense open subscheme of the source whose induced map to the target is locally
  quasi-finite. -/
  existsDenseOpenLocallyQuasiFinite :
    ∃ U : X.Opens, Dense (U : Set X) ∧ LocallyQuasiFinite (U.ι ≫ f)

/-- A morphism is generically finite on the source exactly when its restriction to some dense
open subscheme of the source is locally quasi-finite. -/
theorem genericallyFiniteOnSource_iff {X Y : Scheme.{u}} (f : X ⟶ Y) :
    f.GenericallyFiniteOnSource ↔
      ∃ U : X.Opens, Dense (U : Set X) ∧ LocallyQuasiFinite (U.ι ≫ f) := sorry

/-- Every locally quasi-finite morphism is generically finite on the source. -/
instance instGenericallyFiniteOnSourceOfLocallyQuasiFinite
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] :
    f.GenericallyFiniteOnSource := sorry

/-- A quasi-compact, locally finite type morphism that is generically finite on the source is
generically finite on the target when the target has finitely many irreducible components on
quasi-compact opens. -/
theorem genericallyFiniteOnTarget_of_genericallyFiniteOnSource
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y]
    (hf : f.GenericallyFiniteOnSource) :
    f.GenericallyFiniteOnTarget := sorry

/-- Under the standard finiteness hypotheses, being generically finite on the source canonically
provides being generically finite on the target. -/
instance instGenericallyFiniteOnTargetOfGenericallyFiniteOnSource
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [QuasiCompact f]
    [HasFiniteIrreducibleComponentsOnCompactOpens Y] [f.GenericallyFiniteOnSource] :
    f.GenericallyFiniteOnTarget :=
  genericallyFiniteOnTarget_of_genericallyFiniteOnSource f inferInstance

end AlgebraicGeometry.Scheme.Hom
