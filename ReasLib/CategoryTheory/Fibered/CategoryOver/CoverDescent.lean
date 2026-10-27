/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Descent.DescentData
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Pseudofunctor
public import ReasLib.CategoryTheory.Sites.Cover.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Descent along a bundled cover

This file names the descent functor associated to a bundled Grothendieck cover and exposes the
fully faithful preimage API independently of any global stack assumption. Stack-specific closure
and characterization results can therefore specialize this owner without rebuilding it.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.GrothendieckTopology.Cover.Descent

open CategoryTheory Limits

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]
variable {J : GrothendieckTopology C} {U : C}

/-- The canonical descent functor of a fibred category along a bundled cover. -/
@[stacks 02ZF "descent functor of a bundled cover"]
noncomputable abbrev functor
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] :
    p.Fiber U ⥤
      (Functor.fiberPseudofunctor p).DescentData (fun I : T.Arrow ↦ I.f) :=
  (Functor.fiberPseudofunctor p).toDescentData (fun I : T.Arrow ↦ I.f)

/-- The canonical preimage of a morphism under a fully faithful cover descent functor. -/
@[stacks 02ZF "fully faithful cover-descent preimage"]
noncomputable def hom
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] {x y : p.Fiber U}
    [(functor T p).Full] [(functor T p).Faithful]
    (d : (functor T p).obj x ⟶ (functor T p).obj y) : x ⟶ y :=
  (Functor.FullyFaithful.ofFullyFaithful (functor T p)).preimage d

/-- Mapping the canonical cover-descent preimage recovers the original morphism. -/
@[simp, stacks 02ZF "cover-descent preimage computation"]
theorem map_hom
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] {x y : p.Fiber U}
    [(functor T p).Full] [(functor T p).Faithful]
    (d : (functor T p).obj x ⟶ (functor T p).obj y) :
    (functor T p).map (hom T p d) = d := by
  exact (Functor.FullyFaithful.ofFullyFaithful (functor T p)).map_preimage d

/-- A fiber morphism is the canonical cover-descent preimage exactly when it maps to the
prescribed descent morphism. -/
@[stacks 02ZF "cover-descent preimage characterization"]
theorem eq_hom_iff
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] {x y : p.Fiber U}
    [(functor T p).Full] [(functor T p).Faithful]
    (d : (functor T p).obj x ⟶ (functor T p).obj y) (f : x ⟶ y) :
    f = hom T p d ↔ (functor T p).map f = d := by
  constructor
  · rintro rfl
    exact map_hom T p d
  · intro h
    apply (functor T p).map_injective
    exact h.trans (map_hom T p d).symm

/-- A faithful cover descent functor detects equality of fiber morphisms. -/
@[stacks 02ZF "faithful cover-descent hom extensionality"]
theorem hom_ext
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] [(functor T p).Faithful]
    {x y : p.Fiber U} {f g : x ⟶ y}
    (h : (functor T p).map f = (functor T p).map g) : f = g := by
  exact (functor T p).map_injective h

/-- Equality with a morphism of cover descent data can be checked on every component. -/
@[stacks 02ZF "cover-descent morphism component extensionality"]
theorem map_eq_of_components
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] {x y : p.Fiber U}
    (f : x ⟶ y) (d : (functor T p).obj x ⟶ (functor T p).obj y)
    (h : ∀ I : T.Arrow,
      ((Functor.fiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map f = d.hom I) :
    (functor T p).map f = d := by
  exact Pseudofunctor.DescentData.hom_ext h

/-- A faithful cover descent functor detects equality from equality on every component. -/
@[stacks 02ZF "faithful cover-descent componentwise hom extensionality"]
theorem hom_ext_of_components
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] [(functor T p).Faithful]
    {x y : p.Fiber U} {f g : x ⟶ y}
    (h : ∀ I : T.Arrow,
      ((Functor.fiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map f =
        ((Functor.fiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map g) :
    f = g := by
  apply hom_ext T p
  exact map_eq_of_components T p f ((functor T p).map g) h

/-- Every morphism in the target of a fully faithful cover descent functor has a unique
fiber-morphism preimage. -/
@[stacks 02ZF "unique cover-descent morphism preimage"]
theorem existsUnique_hom
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered]
    [(functor T p).Full] [(functor T p).Faithful]
    {x y : p.Fiber U} (d : (functor T p).obj x ⟶ (functor T p).obj y) :
    ∃! f : x ⟶ y, (functor T p).map f = d := by
  refine ⟨hom T p d, map_hom T p d, ?_⟩
  intro f hf
  exact (eq_hom_iff T p d f).2 hf

/-- Every compatible component family in cover descent data has a unique fiber-morphism
preimage under a fully faithful descent functor. -/
@[stacks 02ZF "unique componentwise cover-descent morphism preimage"]
theorem existsUnique_hom_of_components
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered]
    [(functor T p).Full] [(functor T p).Faithful]
    {x y : p.Fiber U} (d : (functor T p).obj x ⟶ (functor T p).obj y) :
    ∃! f : x ⟶ y, ∀ I : T.Arrow,
      ((Functor.fiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map f = d.hom I := by
  refine ⟨hom T p d, ?_, ?_⟩
  · intro I
    exact congrArg (fun e ↦ e.hom I) (map_hom T p d)
  · intro f hf
    exact (eq_hom_iff T p d f).2 (map_eq_of_components T p f d hf)

/-- Restricting the canonical cover-descent preimage to a cover arrow recovers the prescribed
component. -/
@[stacks 02ZF "cover-descent preimage component computation"]
theorem hom_component
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered]
    [(functor T p).Full] [(functor T p).Faithful]
    {x y : p.Fiber U} (d : (functor T p).obj x ⟶ (functor T p).obj y)
    (I : T.Arrow) :
    ((Functor.fiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map (hom T p d) =
      d.hom I := by
  exact congrArg (fun e ↦ e.hom I) (map_hom T p d)

/-- A fiber morphism with the prescribed cover-descent components is the canonical preimage. -/
@[stacks 02ZF "cover-descent preimage from components"]
theorem eq_hom_of_components
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered]
    [(functor T p).Full] [(functor T p).Faithful]
    {x y : p.Fiber U} (d : (functor T p).obj x ⟶ (functor T p).obj y)
    (f : x ⟶ y)
    (h : ∀ I : T.Arrow,
      ((Functor.fiberPseudofunctor p).map I.f.op.toLoc).toFunctor.map f = d.hom I) :
    f = hom T p d := by
  exact (eq_hom_iff T p d f).2 (map_eq_of_components T p f d h)

/-- The canonical preimage of an isomorphism under a fully faithful cover descent functor is an
isomorphism. -/
@[stacks 02ZF "cover-descent preimage preserves isomorphisms"]
instance hom_isIso
    (T : J.Cover U) (p : S ⥤ C) [p.IsFibered] {x y : p.Fiber U}
    [(functor T p).Full] [(functor T p).Faithful]
    (d : (functor T p).obj x ⟶ (functor T p).obj y) [IsIso d] :
    IsIso (hom T p d) := by
  haveI : IsIso ((functor T p).map (hom T p d)) := by
    rw [map_hom]
    infer_instance
  exact isIso_of_fully_faithful (functor T p) (hom T p d)

/- Axiom audit: `functor` is the canonical fiber-pseudofunctor descent construction, while
`hom` uses only the standard fully faithful preimage choice. -/

end CategoryTheory.GrothendieckTopology.Cover.Descent
