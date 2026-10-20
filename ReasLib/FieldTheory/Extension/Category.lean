/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.RingTheory.EssentialFiniteness
public import Mathlib.RingTheory.AlgebraicIndependent.Basic

/-!
# Finitely generated field extensions

This file packages finitely generated field extensions of a fixed field as a
full subcategory of commutative algebras.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace AlgebraicGeometry.FinitelyGeneratedFieldExtension

/-- The property that a commutative `k`-algebra is a field finitely generated over `k`. -/
def property (k : Type u) [Field k] : ObjectProperty (CommAlgCat.{v} k) :=
  fun K ↦ IsField K ∧ Algebra.EssFiniteType k K

/-- The category of finitely generated field extensions of `k` and `k`-algebra maps. -/
abbrev Cat (k : Type u) [Field k] :=
  (property k).FullSubcategory

/-- The object property of having transcendence degree one over the base field. -/
def trdegOneProperty (k : Type u) [Field k] : ObjectProperty (Cat.{u, v} k) :=
  fun K ↦ Algebra.trdeg k K.obj = 1

/-- Finitely generated field extensions of `k` of transcendence degree one. -/
abbrev TranscendenceDegreeOne (k : Type u) [Field k] :=
  (trdegOneProperty k).FullSubcategory

/-- An object of `TranscendenceDegreeOne k` has transcendence degree one over `k`. -/
theorem TranscendenceDegreeOne.trdeg_eq_one {k : Type u} [Field k]
    (K : TranscendenceDegreeOne.{u, v} k) : Algebra.trdeg k K.obj.obj = 1 := K.property

/-- Bundle a finitely generated extension of transcendence degree one as a function field. -/
def TranscendenceDegreeOne.of (k : Type u) [Field k] (K : Type v) [Field K] [Algebra k K]
    [Algebra.EssFiniteType k K] (htrdeg : Algebra.trdeg k K = 1) :
    TranscendenceDegreeOne.{u, v} k :=
  ⟨⟨CommAlgCat.of k K, ⟨Field.toIsField K, inferInstance⟩⟩, htrdeg⟩

end AlgebraicGeometry.FinitelyGeneratedFieldExtension
