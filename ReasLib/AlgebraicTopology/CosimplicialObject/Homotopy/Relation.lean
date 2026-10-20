/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Homotopy.Functoriality
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 019W

# The cosimplicial homotopy relation

This file owns the directed cotensor-valued relation and its finite-zigzag equivalence closure.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe v u v' u'

namespace CategoryTheory.CosimplicialObject

variable {C : Type u} [Category.{v} C]

section Homotopy

variable {U V : CosimplicialObject C}
variable [HasCotensor (Δ[1] : SSet.{0}) V]

/-- The directed cotensor-valued cosimplicial-homotopy relation. This is the one-step relation
whose equivalence closure is `Homotopic`. -/
@[stacks 019W "directed cotensor-valued cosimplicial homotopy"]
def DirectedHomotopy (f g : U ⟶ V) : Prop :=
  Nonempty (Homotopy f g)

/-- A concrete cotensor-valued homotopy supplies a directed homotopy step. -/
@[stacks 019W "concrete cosimplicial homotopy gives a directed step"]
theorem DirectedHomotopy.of_homotopy {a b : U ⟶ V}
    (h : Homotopy a b) : DirectedHomotopy a b := sorry

/-- Equality of cosimplicial morphisms supplies a directed homotopy step. -/
@[stacks 019W "equal cosimplicial morphisms give a directed step"]
theorem DirectedHomotopy.of_eq {a b : U ⟶ V} (h : a = b) :
    DirectedHomotopy a b := sorry

/-- Directed cotensor-valued cosimplicial homotopy is reflexive. -/
@[refl, stacks 019W "directed cosimplicial homotopy is reflexive"]
theorem DirectedHomotopy.refl (a : U ⟶ V) : DirectedHomotopy a a := sorry

/-- Precomposition preserves directed cotensor-valued cosimplicial homotopy. -/
@[stacks 08RJ "cosimplicial dual of precomposition preservation"]
theorem DirectedHomotopy.precomp {T : CosimplicialObject C} {a b : U ⟶ V}
    (h : DirectedHomotopy a b) (p : T ⟶ U) :
    DirectedHomotopy (p ≫ a) (p ≫ b) := sorry

/-- Postcomposition preserves directed cotensor-valued cosimplicial homotopy. -/
@[stacks 08RJ "cosimplicial dual of postcomposition preservation"]
theorem DirectedHomotopy.postcomp {W : CosimplicialObject C}
    [HasCotensor (Δ[1] : SSet.{0}) W] {a b : U ⟶ V}
    (h : DirectedHomotopy a b) (p : V ⟶ W) :
    DirectedHomotopy (a ≫ p) (b ≫ p) := sorry

/-- Simultaneous precomposition and postcomposition preserve directed cotensor-valued
cosimplicial homotopy. -/
@[stacks 08RJ "cosimplicial dual of two-sided composition preservation"]
theorem DirectedHomotopy.precomp_postcomp {T W : CosimplicialObject C}
    [HasCotensor (Δ[1] : SSet.{0}) W] {a b : U ⟶ V}
    (h : DirectedHomotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    DirectedHomotopy (p ≫ a ≫ q) (p ≫ b ≫ q) := sorry

/-- Two morphisms of cosimplicial objects are homotopic if they are connected by a finite
zigzag of directed cosimplicial homotopies. -/
@[stacks 019W "cosimplicial homotopy relation"]
def Homotopic (a b : U ⟶ V) : Prop :=
  Relation.EqvGen DirectedHomotopy a b

/-- Cosimplicial homotopy is reflexive. -/
@[refl, stacks 019W "cosimplicial homotopy is reflexive"]
lemma Homotopic.refl (a : U ⟶ V) : Homotopic a a := sorry

/-- Cosimplicial homotopy is symmetric. -/
@[symm, stacks 019W "cosimplicial homotopy is symmetric"]
lemma Homotopic.symm {a b : U ⟶ V} (h : Homotopic a b) : Homotopic b a := sorry

/-- Cosimplicial homotopy is transitive. -/
@[trans, stacks 019W "cosimplicial homotopy is transitive"]
lemma Homotopic.trans {a b c : U ⟶ V}
    (hab : Homotopic a b) (hbc : Homotopic b c) : Homotopic a c := sorry

/-- A concrete cotensor-valued cosimplicial homotopy promotes to the zigzag relation. -/
@[stacks 019W "concrete cosimplicial homotopy belongs to the zigzag relation"]
lemma Homotopic.of_homotopy {a b : U ⟶ V} (h : Homotopy a b) : Homotopic a b := sorry

/-- A directed cotensor-valued homotopy step belongs to its generated zigzag relation. -/
@[stacks 019W "directed cosimplicial homotopy belongs to the zigzag relation"]
lemma Homotopic.of_directed {a b : U ⟶ V}
    (h : DirectedHomotopy a b) : Homotopic a b := sorry

/-- Equal cosimplicial morphisms belong to the zigzag homotopy relation. -/
@[stacks 019W "equal morphisms are zigzag cosimplicially homotopic"]
lemma Homotopic.of_eq {a b : U ⟶ V} (h : a = b) : Homotopic a b := sorry

/-- A map on morphisms that carries directed homotopies to homotopic morphisms preserves the
zigzag cosimplicial homotopy relation. -/
@[stacks 019W "maps preserve the zigzag cosimplicial homotopy relation"]
theorem Homotopic.map
    {a b : U ⟶ V} (h : Homotopic a b)
    {D : Type u'} [Category.{v'} D]
    {U' V' : CosimplicialObject D}
    [HasCotensor (Δ[1] : SSet.{0}) V']
    (F : (U ⟶ V) → (U' ⟶ V'))
    (hF : ∀ {x y : U ⟶ V}, DirectedHomotopy x y → Homotopic (F x) (F y)) :
    Homotopic (F a) (F b) := sorry

/-- Precomposition preserves the zigzag cosimplicial homotopy relation. -/
@[stacks 08RJ "cosimplicial dual of zigzag precomposition preservation"]
theorem Homotopic.precomp {T : CosimplicialObject C} {a b : U ⟶ V}
    (h : Homotopic a b) (p : T ⟶ U) :
    Homotopic (p ≫ a) (p ≫ b) := sorry

/-- Postcomposition preserves the zigzag cosimplicial homotopy relation. -/
@[stacks 08RJ "cosimplicial dual of zigzag postcomposition preservation"]
theorem Homotopic.postcomp {W : CosimplicialObject C}
    [HasCotensor (Δ[1] : SSet.{0}) W] {a b : U ⟶ V}
    (h : Homotopic a b) (p : V ⟶ W) :
    Homotopic (a ≫ p) (b ≫ p) := sorry

/-- Simultaneous precomposition and postcomposition preserve the zigzag cosimplicial homotopy
relation. -/
@[stacks 08RJ "cosimplicial dual of zigzag two-sided composition preservation"]
theorem Homotopic.precomp_postcomp {T W : CosimplicialObject C}
    [HasCotensor (Δ[1] : SSet.{0}) W] {a b : U ⟶ V}
    (h : Homotopic a b) (p : T ⟶ U) (q : V ⟶ W) :
    Homotopic (p ≫ a ≫ q) (p ≫ b ≫ q) := sorry

end Homotopy

end CategoryTheory.CosimplicialObject
