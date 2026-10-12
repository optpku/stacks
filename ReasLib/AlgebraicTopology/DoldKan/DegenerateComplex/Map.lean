/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- The simplicial component restricted to a degenerate subobject factors through the target
degenerate subobject. -/
@[stacks 019A "degenerate-complex map component factorization"]
theorem map.app.factors {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (degenerateSubobject V n).Factors
      ((degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌)) := sorry

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
      (degenerateSubobject U n).arrow ≫ f.app (Opposite.op ⦋n⦌) := sorry

/-- The degreewise maps induced by a simplicial morphism commute with the differentials. -/
@[stacks 019A "degenerate-complex map commutes with differentials"]
theorem map.comm {U V : SimplicialObject C} (f : U ⟶ V) (i j : ℕ)
    (hij : (ComplexShape.down ℕ).Rel i j) :
    map.app f i ≫ (D[V]).d i j = (D[U]).d i j ≫ map.app f j := sorry

/-- The morphism of degenerate complexes induced by a simplicial morphism. -/
@[stacks 019A "degenerate-complex map"]
def map {U V : SimplicialObject C} (f : U ⟶ V) : D[U] ⟶ D[V] where
  f n := map.app f n
  comm' := map.comm f

/-- The degree-`n` component of a degenerate-complex map is `map.app`. -/
@[simp, stacks 019A "degenerate-complex map component projection"]
theorem map.f {U V : SimplicialObject C} (f : U ⟶ V) (n : ℕ) :
    (map f).f n = map.app f n := sorry

/-- The degenerate-complex map is compatible with the canonical inclusions into alternating-face
complexes. -/
@[reassoc, stacks 019A "degenerate inclusion naturality"]
theorem ι.naturality {U V : SimplicialObject C} (f : U ⟶ V) :
    map f ≫ ι V = ι U ≫ (alternatingFaceMapComplex C).map f := sorry

/-- The identity simplicial morphism induces the identity degenerate-complex morphism. -/
@[stacks 019A "degenerate-complex identity map"]
theorem map.id (U : SimplicialObject C) :
    degenerateComplex.map (𝟙 U) = 𝟙 D[U] := sorry

/-- Composition of simplicial morphisms induces composition on degenerate complexes. -/
@[stacks 019A "degenerate-complex composition map"]
theorem map.comp {U V W : SimplicialObject C} (f : U ⟶ V) (g : V ⟶ W) :
    degenerateComplex.map (f ≫ g) = degenerateComplex.map f ≫ degenerateComplex.map g := sorry

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
    (degenerateComplex.functor (C := C)).obj U = D[U] := sorry

/-- The map value of the degenerate-complex functor. -/
@[simp, stacks 019A "degenerate-complex functor map formula"]
theorem functor.map {U V : SimplicialObject C} (f : U ⟶ V) :
    (degenerateComplex.functor (C := C)).map f = degenerateComplex.map f := sorry

/-- The inclusion of degenerate complexes into alternating-face complexes is natural. -/
@[stacks 019A "degenerate inclusion natural transformation"]
def ι.natTrans : degenerateComplex.functor (C := C) ⟶ alternatingFaceMapComplex C where
  app U := ι U
  naturality _ _ f := ι.naturality f

/-- The inclusion natural transformation has component `ι U` at `U`. -/
@[simp, stacks 019A "degenerate inclusion natural transformation component"]
theorem ι.natTrans.app (U : SimplicialObject C) :
    (ι.natTrans (C := C)).app U = ι U := sorry

end degenerateComplex

end AlgebraicTopology.DoldKan
