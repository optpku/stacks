/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Atlas
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.InternalHom.Bidual

/-! # Derived sheaf Hom on an algebraic space

The original-universe atlas comparison transports the sheaf-valued internal Hom and its
canonical evaluation map from the small ringed site to algebraic-space module sheaves.
-/

@[expose] public section

open CategoryTheory Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Derived sheaf Hom into a fixed complex, contravariant in its source. -/
def sourceFunctor (N : ModuleDerived X) : (ModuleDerived X)ᵒᵖ ⥤ ModuleDerived X :=
  (Modules.Atlas.derivedEquivalence X).functor.op ⋙
    RingedSite.Hom.ModuleDerived.InternalHom.sourceFunctor (J := Modules.Atlas.topology X)
      (O := Modules.Atlas.commStructureSheaf X)
      ((Modules.Atlas.derivedEquivalence X).functor.obj N) ⋙
    (Modules.Atlas.derivedEquivalence X).inverse

/-- The derived sheaf Hom of two complexes of modules on the algebraic space. -/
def obj (L N : ModuleDerived X) : ModuleDerived X :=
  (sourceFunctor N).obj (op L)

/-- The source functor evaluates to the derived sheaf Hom object. -/
@[simp]
theorem sourceFunctor_obj (N L : ModuleDerived X) :
    (sourceFunctor N).obj (op L) = obj L N := rfl

/-- Derived sheaf Hom is computed by the small atlas and transported back by extension. -/
theorem obj_atlas (L N : ModuleDerived X) :
    obj L N = (Modules.Atlas.derivedEquivalence X).inverse.obj
      (RingedSite.Hom.ModuleDerived.InternalHom.obj (J := Modules.Atlas.topology X)
      (O := Modules.Atlas.commStructureSheaf X)
        ((Modules.Atlas.derivedEquivalence X).functor.obj L)
        ((Modules.Atlas.derivedEquivalence X).functor.obj N)) := rfl

/-- Canonical derived evaluation into the double sheaf-Hom dual. -/
def toBidualApp (N L : ModuleDerived X) : L ⟶ obj (obj L N) N :=
  let e := Modules.Atlas.derivedEquivalence X
  let D := RingedSite.Hom.ModuleDerived.InternalHom.sourceFunctor (J := Modules.Atlas.topology X)
      (O := Modules.Atlas.commStructureSheaf X) (e.functor.obj N)
  e.unitIso.hom.app L ≫
    e.inverse.map (RingedSite.Hom.ModuleDerived.InternalHom.toBidualApp (J := Modules.Atlas.topology X)
      (O := Modules.Atlas.commStructureSheaf X)
      (e.functor.obj N) (e.functor.obj L) ≫
      D.map (e.counitIso.hom.app (D.obj (op (e.functor.obj L)))).op)

/-- Restriction of derived evaluation is the canonical evaluation on the small atlas,
under the counit comparisons for the two sheaf-Hom objects. -/
theorem toBidualApp_atlas (N L : ModuleDerived X) :
    let e := Modules.Atlas.derivedEquivalence X
    let D := RingedSite.Hom.ModuleDerived.InternalHom.sourceFunctor (J := Modules.Atlas.topology X)
      (O := Modules.Atlas.commStructureSheaf X) (e.functor.obj N)
    e.functor.map (toBidualApp N L) ≫
      e.counitIso.hom.app (D.obj (op (e.functor.obj (obj L N)))) ≫
      D.map (e.counitIso.inv.app (D.obj (op (e.functor.obj L)))).op =
        RingedSite.Hom.ModuleDerived.InternalHom.toBidualApp (J := Modules.Atlas.topology X)
      (O := Modules.Atlas.commStructureSheaf X)
          (e.functor.obj N) (e.functor.obj L) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived.InternalHom
