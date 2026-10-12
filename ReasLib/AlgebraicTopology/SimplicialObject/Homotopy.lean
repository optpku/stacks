/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 08RJ

# Zigzag simplicial homotopy relation

Shared library for the zigzag simplicial homotopy relation on morphisms of simplicial objects.

Defines `DirectedHomotopy` (existence of a canonical simplicial-object homotopy) and `Homotopic`
(its equivalence closure via `Relation.EqvGen`), together with the basic API: reflexivity, symmetry,
transitivity, promotion from a directed homotopy, and compatibility with pre/postcomposition and
functorial whiskering. -/

@[expose] public section

open CategoryTheory Opposite SimplexCategory Simplicial

universe u v u' v'

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

namespace Homotopy

variable {U V W T : SimplicialObject C}
variable {a b : U ⟶ V}

/-- Simultaneously precompose and postcompose a simplicial homotopy. -/
@[stacks 08RJ "two-sided composition of simplicial homotopies"]
def precompPostcomp (H : Homotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    Homotopy (p ≫ a ≫ q) (p ≫ b ≫ q) :=
  (H.postcomp q).precomp p

namespace precompPostcomp

/-- Two-sided composition acts on each simplicial homotopy component by the expected composite. -/
@[simp, stacks 08RJ "components of two-sided simplicial homotopy composition"]
theorem h (H : Homotopy a b) (p : T ⟶ U) (q : V ⟶ W)
    {n : ℕ} (i : Fin (n + 1)) :
    (H.precompPostcomp p q).h i =
      p.app (op ⦋n⦌) ≫ H.h i ≫ q.app (op ⦋n + 1⦌) := sorry

end precompPostcomp

end Homotopy

/-- Evaluating a concrete homotopy between functor-valued simplicial objects at an object
retains the complete homotopy data. -/
@[stacks 019Y "objectwise evaluation of a simplicial homotopy"]
def Homotopy.app {D : Type u'} [Category.{v'} D]
    {X Y : SimplicialObject (C ⥤ D)} {f g : X ⟶ Y}
    (H : Homotopy f g) (A : C) :
    Homotopy (NatTrans.flipApp f A) (NatTrans.flipApp g A) :=
  H.whiskerRight ((evaluation C D).obj A)

namespace Homotopy.app

/-- A homotopy component evaluates pointwise. -/
@[simp, stacks 019Y "objectwise component of a simplicial homotopy"]
theorem h {D : Type u'} [Category.{v'} D]
    {X Y : SimplicialObject (C ⥤ D)} {f g : X ⟶ Y}
    (H : Homotopy f g) (A : C) {n : ℕ} (i : Fin (n + 1)) :
    (H.app A).h i = (H.h i).app A := sorry

end Homotopy.app

section

variable {U V W T : SimplicialObject C}
variable {a b c : U ⟶ V}

/-- Transport the constant simplicial homotopy along an equality of morphisms. -/
@[stacks 07KA "equal morphisms are simplicially homotopic"]
def Homotopy.ofEq (h : a = b) : Homotopy a b :=
  h ▸ Homotopy.refl a

/-- The components of the equality-transport homotopy are those of the constant homotopy. -/
@[simp, stacks 07KA "component of an equality-transport simplicial homotopy"]
theorem Homotopy.ofEq.h (h : a = b) {n : ℕ} (i : Fin (n + 1)) :
    (Homotopy.ofEq h).h i = U.σ i ≫ a.app (op ⦋n + 1⦌) := sorry

/-- Transport a simplicial homotopy along equalities of its source and target morphisms. -/
@[stacks 019K "endpoint transport for simplicial homotopies"]
def Homotopy.cast {a b a' b' : U ⟶ V}
    (ha : a = a') (hb : b = b') (H : Homotopy a b) : Homotopy a' b' :=
  ha ▸ hb ▸ H

/-- The component family is unchanged by endpoint transport. -/
@[simp, stacks 019K "component formula for transported simplicial homotopies"]
theorem Homotopy.cast.h {a b a' b' : U ⟶ V}
    (ha : a = a') (hb : b = b') (H : Homotopy a b)
    {n : ℕ} (i : Fin (n + 1)) :
    (Homotopy.cast ha hb H).h i = H.h i := sorry

/-- The directed simplicial-homotopy relation: `f` and `g` are related when there exists a
canonical simplicial-object homotopy from `f` to `g`. This is the generating relation whose
equivalence closure is `Homotopic`. -/
@[stacks 019K "directed simplicial homotopy"]
def DirectedHomotopy {X Y : SimplicialObject C} (f g : X ⟶ Y) : Prop :=
  Nonempty (Homotopy f g)

/-- A concrete simplicial homotopy supplies a directed homotopy step. -/
@[stacks 019K "concrete simplicial homotopy gives a directed step"]
theorem DirectedHomotopy.of_homotopy (h : Homotopy a b) : DirectedHomotopy a b := sorry

/-- Equality of simplicial morphisms supplies a directed homotopy step. -/
@[stacks 019K "equal simplicial morphisms give a directed step"]
theorem DirectedHomotopy.of_eq (h : a = b) : DirectedHomotopy a b := sorry

/-- Directed simplicial homotopy is reflexive. -/
@[refl, stacks 019K "directed simplicial homotopy is reflexive"]
theorem DirectedHomotopy.refl (a : U ⟶ V) : DirectedHomotopy a a := sorry

/-- Precomposition preserves directed simplicial homotopy. -/
@[stacks 08RJ "precomposition preserves directed simplicial homotopy"]
theorem DirectedHomotopy.precomp (h : DirectedHomotopy a b) (p : T ⟶ U) :
    DirectedHomotopy (p ≫ a) (p ≫ b) := sorry

/-- Postcomposition preserves directed simplicial homotopy. -/
@[stacks 08RJ "postcomposition preserves directed simplicial homotopy"]
theorem DirectedHomotopy.postcomp (h : DirectedHomotopy a b) (p : V ⟶ W) :
    DirectedHomotopy (a ≫ p) (b ≫ p) := sorry

/-- Simultaneous precomposition and postcomposition preserve directed simplicial homotopy. -/
@[stacks 08RJ "two-sided composition preserves directed simplicial homotopy"]
theorem DirectedHomotopy.precomp_postcomp
    (h : DirectedHomotopy a b) (p : T ⟶ U) (q : V ⟶ W) :
    DirectedHomotopy (p ≫ a ≫ q) (p ≫ b ≫ q) := sorry

/-- Applying a functor degreewise preserves directed simplicial homotopy. -/
@[stacks 019Y "functors preserve directed simplicial homotopy"]
theorem DirectedHomotopy.whiskerRight
    {D : Type u'} [Category.{v'} D]
    (h : DirectedHomotopy a b) (F : C ⥤ D) :
    DirectedHomotopy (Functor.whiskerRight a F) (Functor.whiskerRight b F) := sorry

/-- Two morphisms `a, b : U ⟶ V` are homotopic if they are connected by a finite zigzag of
directed simplicial homotopies in either direction, where a directed homotopy from `a` to `b`
is the canonical simplicial-object homotopy `CategoryTheory.SimplicialObject.Homotopy a b`. -/
@[stacks 019K "simplicial homotopy relation"]
def Homotopic (a b : U ⟶ V) : Prop :=
  Relation.EqvGen DirectedHomotopy a b

/-- Simplicial homotopy is reflexive. -/
@[refl, stacks 019K "simplicial homotopy is reflexive"]
lemma Homotopic.refl (a : U ⟶ V) : Homotopic a a := sorry

/-- Equal morphisms are related by zigzag simplicial homotopy. -/
@[stacks 019K "equal morphisms are zigzag simplicially homotopic"]
lemma Homotopic.of_eq (h : a = b) : Homotopic a b := sorry

/-- Simplicial homotopy is symmetric. -/
@[symm, stacks 019K "simplicial homotopy is symmetric"]
lemma Homotopic.symm (h : Homotopic a b) : Homotopic b a := sorry

/-- Simplicial homotopy is transitive. -/
@[trans, stacks 019K "simplicial homotopy is transitive"]
lemma Homotopic.trans (hab : Homotopic a b) (hbc : Homotopic b c) : Homotopic a c :=
  sorry

/-- A concrete simplicial homotopy gives the associated zigzag homotopy relation. -/
@[stacks 019K "concrete simplicial homotopy belongs to the zigzag relation"]
lemma Homotopic.of_homotopy (h : Homotopy a b) : Homotopic a b := sorry

/-- A directed simplicial homotopy step belongs to its generated zigzag relation. -/
@[stacks 019K "directed simplicial homotopy belongs to the zigzag relation"]
lemma Homotopic.of_directed (h : DirectedHomotopy a b) : Homotopic a b := sorry

/-- Any map on morphisms that sends directed simplicial homotopies to zigzag homotopies also
preserves the induced zigzag homotopy relation. -/
@[stacks 019Y "maps preserve the zigzag simplicial homotopy relation"]
theorem Homotopic.map
    (h : Homotopic a b)
    {D : Type u'} [Category.{v'} D]
    {U' V' : SimplicialObject D}
    (F : (U ⟶ V) → (U' ⟶ V'))
    (hF : ∀ {x y : U ⟶ V}, DirectedHomotopy x y → Homotopic (F x) (F y))
    : Homotopic (F a) (F b) := sorry

/-- Precomposing preserves the zigzag simplicial homotopy relation. -/
@[stacks 08RJ "precomposition preserves simplicial homotopy"]
lemma Homotopic.precomp (h : Homotopic a b) (p : T ⟶ U) :
    Homotopic (p ≫ a) (p ≫ b) := sorry

/-- Postcomposing preserves the zigzag simplicial homotopy relation. -/
@[stacks 08RJ "postcomposition preserves simplicial homotopy"]
lemma Homotopic.postcomp (h : Homotopic a b) (p : V ⟶ W) :
    Homotopic (a ≫ p) (b ≫ p) := sorry

/-- Simultaneous precomposition and postcomposition preserve the zigzag simplicial homotopy
relation. -/
@[stacks 08RJ "two-sided composition preserves simplicial homotopy"]
lemma Homotopic.precomp_postcomp (h : Homotopic a b) (p : T ⟶ U) (q : V ⟶ W) :
    Homotopic (p ≫ a ≫ q) (p ≫ b ≫ q) := sorry

/-- Functors preserve the zigzag relation generated by directed simplicial homotopies. -/
@[stacks 019Y "functors preserve the zigzag simplicial homotopy relation"]
theorem Homotopic.whiskerRight
    {D : Type*} [Category D]
    (h : Homotopic a b) (F : C ⥤ D) :
    Homotopic (Functor.whiskerRight a F) (Functor.whiskerRight b F) := sorry

end

end CategoryTheory.SimplicialObject
