/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.Relation
public import ReasLib.CategoryTheory.HomRel.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Simplicial homotopy equivalences

Specializes the reusable `HomRel.Equiv` API to simplicial homotopy.  It also defines the
derived morphism property `homotopyEquivalences C` and the proposition alias
`IsHomotopyEquivalence`; relation-level reflexivity, symmetry, transitivity, isomorphism, and
functoriality remain owned by `HomRel.Equiv`.
-/

@[expose] public section

universe u v

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

/-- A simplicial homotopy equivalence is an equivalence modulo the simplicial homotopy
relation.  Its inverse laws are available as `hom_inv_id` and `inv_hom_id`. -/
@[stacks 019N "simplicial homotopy equivalence"]
abbrev HomotopyEquiv (U V : SimplicialObject C) :=
  HomRel.Equiv (homotopyRel C) U V

variable (C : Type u) [Category.{v} C] in
/-- The morphism property on simplicial objects obtained by specializing equivalences modulo a
relation to the simplicial homotopy relation. -/
@[stacks 019N "simplicial homotopy-equivalence morphism property"]
abbrev homotopyEquivalences : MorphismProperty (SimplicialObject C) :=
  HomRel.equivalences (homotopyRel C)

/-- A morphism of simplicial objects is a homotopy equivalence if it is the forward morphism of
some simplicial homotopy equivalence. -/
@[stacks 019N "simplicial homotopy-equivalence predicate"]
abbrev IsHomotopyEquivalence {U V : SimplicialObject C} (a : U ⟶ V) : Prop :=
  homotopyEquivalences C a

namespace IsHomotopyEquivalence

/-- A simplicial morphism is a homotopy equivalence exactly when it is the forward map of
structured simplicial homotopy-equivalence data. -/
@[stacks 019N "structured witness criterion for a simplicial homotopy equivalence"]
theorem iff_exists_equiv {U V : SimplicialObject C} (f : U ⟶ V) :
    IsHomotopyEquivalence f ↔ ∃ e : HomotopyEquiv U V, e.hom = f := sorry

/-- A simplicial morphism is a homotopy equivalence exactly when it admits a morphism in the
opposite direction whose two composites are homotopic to the corresponding identities. -/
@[stacks 019N "homotopy-equivalence inverse criterion"]
theorem iff_exists_inverse {U V : SimplicialObject C} (f : U ⟶ V) :
    IsHomotopyEquivalence f ↔
      ∃ g : V ⟶ U, Homotopic (f ≫ g) (𝟙 U) ∧ Homotopic (g ≫ f) (𝟙 V) := sorry

end IsHomotopyEquivalence

namespace HomotopyEquiv

variable {U V : SimplicialObject C}

/-- The forward map of a simplicial homotopy equivalence is a simplicial homotopy-equivalence
morphism. -/
@[stacks 019N "forward map of a simplicial homotopy equivalence"]
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    IsHomotopyEquivalence e.hom := sorry

end HomotopyEquiv

end CategoryTheory.SimplicialObject
