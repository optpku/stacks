/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Functor.Const
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Finite.Defs
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Objectwise properties of type-valued functors

This file bundles recurring objectwise finiteness and nonemptiness assumptions on a
type-valued functor. The bundled owners keep downstream APIs from repeatedly exposing a
dependent family of typeclass parameters.
-/

@[expose] public section

open CategoryTheory

universe w v u

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C]

/-- A type-valued functor is objectwise finite when each of its values is finite. -/
@[stacks 017E "objectwise finite type-valued functor"]
class ObjFinite (F : C ⥤ Type w) : Prop where
  /-- Every value of an objectwise finite functor is finite. -/
  finite (X : C) : Finite (F.obj X)

/-- A type-valued functor is objectwise nonempty when each of its values is nonempty. -/
@[stacks 017E "objectwise nonempty type-valued functor"]
class ObjNonempty (F : C ⥤ Type w) : Prop where
  /-- Every value of an objectwise nonempty functor is nonempty. -/
  nonempty (X : C) : Nonempty (F.obj X)

attribute [instance 100] ObjFinite.finite ObjNonempty.nonempty

namespace ObjFinite

/-- Precomposition preserves objectwise finiteness. -/
instance (priority := 100) comp {D : Type*} [Category D]
    (G : D ⥤ C) (F : C ⥤ Type w) [F.ObjFinite] : (G ⋙ F).ObjFinite :=
  ⟨fun X ↦ ObjFinite.finite (F := F) (G.obj X)⟩

/-- A constant functor at a finite type is objectwise finite. -/
instance (priority := 100) const (X : Type w) [Finite X] :
    ((Functor.const C).obj X).ObjFinite :=
  ⟨fun _ ↦ inferInstanceAs (Finite X)⟩

/-- Objectwise finiteness is invariant under natural isomorphism. -/
theorem ofIso {F G : C ⥤ Type w} (e : F ≅ G) [F.ObjFinite] : G.ObjFinite := sorry

end ObjFinite

namespace ObjNonempty

/-- Precomposition preserves objectwise nonemptiness. -/
instance (priority := 100) comp {D : Type*} [Category D]
    (G : D ⥤ C) (F : C ⥤ Type w) [F.ObjNonempty] : (G ⋙ F).ObjNonempty :=
  ⟨fun X ↦ ObjNonempty.nonempty (F := F) (G.obj X)⟩

/-- A constant functor at a nonempty type is objectwise nonempty. -/
instance (priority := 100) const (X : Type w) [Nonempty X] :
    ((Functor.const C).obj X).ObjNonempty :=
  ⟨fun _ ↦ inferInstanceAs (Nonempty X)⟩

/-- Objectwise nonemptiness is invariant under natural isomorphism. -/
theorem ofIso {F G : C ⥤ Type w} (e : F ≅ G) [F.ObjNonempty] : G.ObjNonempty := sorry

end ObjNonempty

end CategoryTheory.Functor
