/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.LocallyGiven.Gluing

/-!
# Compatible isomorphisms of solutions and uniform lower bounds

Compatibility of solution isomorphisms and uniform lower cohomological bounds
are re-exported from the derived-module gluing library.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom RingedSite.ModuleDerived

universe u v w uB vB

#check (RingedSite.ModuleDerived.Solution.IsCompatibleIso :
  ∀ {X : RingedSite.{u, v, w}} {B : Type uB} [Category.{vB} B]
    [UnivLE.{max u v, w}] {D : LocallyGiven.{u, v, w, w, uB, vB} X B}
    (S S' : Solution D), (S.obj ≅ S'.obj) → Prop)

#check (RingedSite.ModuleDerived.Solution.IsCompatibleIso.w :
  ∀ {X : RingedSite.{u, v, w}} {B : Type uB} [Category.{vB} B]
    [UnivLE.{max u v, w}] {D : LocallyGiven.{u, v, w, w, uB, vB} X B}
    {S S' : Solution D} {e : S.obj ≅ S'.obj},
    Solution.IsCompatibleIso S S' e → ∀ U : B,
      (localizedRestrictionDerived.{w} X (D.u.obj U)).map e.hom ≫ (S'.iso U).hom =
        (S.iso U).hom)

#check (RingedSite.ModuleDerived.LocallyGiven.uniformlyBoundedBelow :
  ∀ {X : RingedSite.{u, v, w}} {B : Type uB} [Category.{vB} B]
    [UnivLE.{max u v, w}], LocallyGiven.{u, v, w, w, uB, vB} X B → Prop)

#check (RingedSite.ModuleDerived.LocallyGiven.uniformlyBoundedBelow_iff :
  ∀ {X : RingedSite.{u, v, w}} {B : Type uB} [Category.{vB} B]
    [UnivLE.{max u v, w}] (D : LocallyGiven.{u, v, w, w, uB, vB} X B),
    D.uniformlyBoundedBelow ↔
      ∃ t : ℤ, ∀ (U : B) (i : ℤ), i < t →
        IsZero ((DerivedCategory.homologyFunctor _ i).obj (D.obj U)))
