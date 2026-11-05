/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Differential
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of degreewise degenerate complexes

@stack 019A
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Subobject AlgebraicTopology
open scoped Simplicial DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasZeroObject C] [HasBinaryCoproducts C] [HasImages C]

namespace degenerateComplex

set_option backward.isDefEq.respectTransparency false in
/-- The simplicial component restricted to a degenerate subobject factors through the target
degenerate subobject. -/
@[stacks 019A "degenerate-complex map component factorization"]
theorem map.app.factors {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (degenerateSubobject V n).Factors
      ((degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌)) := by
  apply (factors_iff _ _).2
  refine ⟨(degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌) ≫
    (degenerateSubobject V n).factorThru ((QInfty : K[V] ⟶ K[V]).f n)
      (π.app.factors V n), ?_⟩
  change _ ≫ (degenerateSubobject V n).arrow = _
  simp only [Category.assoc, factorThru_arrow]
  rw [QInfty_f_naturality n f, ← Category.assoc, arrow_comp_QInfty]

/-- The degree-`n` map on degenerate subobjects induced by a simplicial morphism. -/
@[stacks 019A "degenerate-complex map component"]
def map.app {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (degenerateSubobject U n : C) ⟶ (degenerateSubobject V n : C) :=
  (degenerateSubobject V n).factorThru
    ((degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌))
    (map.app.factors f n)

/-- The map on degenerate subobjects agrees after inclusion with the corresponding simplicial
component. -/
@[reassoc, stacks 019A "degenerate-complex map component formula"]
theorem map.app.arrow {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    map.app f n ≫ (degenerateSubobject V n).arrow =
      (degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌) := factorThru_arrow _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The degreewise maps induced by a simplicial morphism commute with the differentials. -/
@[stacks 019A "degenerate-complex map commutes with differentials"]
theorem map.comm {U V : SimplicialObject C} (f : U ⟶ V) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    map.app f i ≫ (D[V]).d i j = (D[U]).d i j ≫ map.app f j := by
  apply (cancel_mono (degenerateSubobject V j).arrow).1
  simp only [Category.assoc, map.app.arrow]
  rw [← ι.comm V i j hij, ← Category.assoc, map.app.arrow, Category.assoc,
    ← Category.assoc ((D[U]).d i j), ← ι.comm U i j hij, Category.assoc]
  exact congrArg (fun morphism => (degenerateSubobject U i).arrow ≫ morphism)
    (((alternatingFaceMapComplex C).map f).comm i j)

/-- The morphism of degenerate complexes induced by a simplicial morphism. -/
@[stacks 019A "degenerate-complex map"]
def map {U V : SimplicialObject C} (f : U ⟶ V) : D[U] ⟶ D[V] where
  f n := map.app f n
  comm' := map.comm f

/-- The degree-`n` component of a degenerate-complex map is `map.app`. -/
@[simp, stacks 019A "degenerate-complex map component projection"]
theorem map.f {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (map f).f n = map.app f n := rfl

/-- The degenerate-complex map is compatible with the canonical inclusions into alternating-face
complexes. -/
@[reassoc, stacks 019A "degenerate inclusion naturality"]
theorem ι.naturality {U V : SimplicialObject C} (f : U ⟶ V) :
    map f ≫ ι V = ι U ≫ (alternatingFaceMapComplex C).map f := by
  ext n
  exact map.app.arrow f n

set_option backward.isDefEq.respectTransparency false in
/-- The identity simplicial morphism induces the identity degenerate-complex morphism. -/
@[stacks 019A "degenerate-complex identity map"]
theorem map.id (U : SimplicialObject C) :
    degenerateComplex.map (𝟙 U) = 𝟙 D[U] := by
  ext n
  apply (cancel_mono (degenerateSubobject U n).arrow).1
  simpa only [map.f, HomologicalComplex.id_f, NatTrans.id_app, Category.id_comp,
    Category.comp_id] using map.app.arrow (𝟙 U) n

set_option backward.isDefEq.respectTransparency false in
/-- Composition of simplicial morphisms induces composition on degenerate complexes. -/
@[stacks 019A "degenerate-complex composition map"]
theorem map.comp {U V W : SimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    degenerateComplex.map (f ≫ g) = degenerateComplex.map f ≫ degenerateComplex.map g := by
  ext n
  apply (cancel_mono (degenerateSubobject W n).arrow).1
  simp only [HomologicalComplex.comp_f, map.f, Category.assoc, map.app.arrow,
    map.app.arrow_assoc, NatTrans.comp_app]

/-- The degenerate-complex construction as a functor on simplicial objects. -/
@[stacks 019A "degenerate-complex functor"]
def functor : SimplicialObject C ⥤ ChainComplex C ℕ where
  obj U := D[U]
  map := degenerateComplex.map
  map_id := degenerateComplex.map.id
  map_comp := degenerateComplex.map.comp

/-- The object value of the degenerate-complex functor. -/
@[simp, stacks 019A "degenerate-complex functor object formula"]
theorem functor.obj (U : SimplicialObject C) :
    (degenerateComplex.functor (C := C)).obj U = D[U] := rfl

/-- The map value of the degenerate-complex functor. -/
@[simp, stacks 019A "degenerate-complex functor map formula"]
theorem functor.map {U V : SimplicialObject C} (f : U ⟶ V) :
    (degenerateComplex.functor (C := C)).map f = degenerateComplex.map f := rfl

/-- The inclusion of degenerate complexes into alternating-face complexes is natural. -/
@[stacks 019A "degenerate inclusion natural transformation"]
def ι.natTrans : degenerateComplex.functor (C := C) ⟶ alternatingFaceMapComplex C where
  app U := ι U
  naturality _ _ f := ι.naturality f

/-- The inclusion natural transformation has component `ι U` at `U`. -/
@[simp, stacks 019A "degenerate inclusion natural transformation component"]
theorem ι.natTrans.app (U : SimplicialObject C) :
    (ι.natTrans (C := C)).app U = ι U := rfl

end degenerateComplex

end AlgebraicTopology.DoldKan
