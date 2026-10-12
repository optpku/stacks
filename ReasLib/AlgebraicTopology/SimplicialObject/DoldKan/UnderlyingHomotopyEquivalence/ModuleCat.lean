/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.DoldKan.UnderlyingHomotopyEquivalence.Functor
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Underlying homotopy equivalences of simplicial modules

This file specializes the functorial detection theorem to the additive-group forgetful functor
from modules.  The morphism property is a reusable owner; its alternating-face and normalized
Moore consequences are separate symmetric inclusions.
-/

@[expose] public section

open CategoryTheory HomologicalComplex
open AlgebraicTopology

universe u v

namespace CategoryTheory.SimplicialObject.ModuleCat.underlying

/-- Simplicial module maps that become homotopy equivalences after forgetting to simplicial
sets. -/
@[stacks 08P2 "underlying homotopy equivalences of simplicial modules"]
def homotopyEquivalences (R : Type u) [Ring R] :
    MorphismProperty (SimplicialObject (ModuleCat.{v} R)) :=
  AddCommGrp.underlying.homotopyEquivalences.inverseImage
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ (ModuleCat.{v} R)
      AddCommGrpCat.{v}).obj (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}))

/-- A simplicial module map belongs to `homotopyEquivalences R` exactly when its underlying
simplicial additive-group map does. -/
@[simp, stacks 08P2 "membership in underlying module homotopy equivalences"]
theorem homotopyEquivalences_iff (R : Type u) [Ring R]
    {X Y : SimplicialObject (ModuleCat.{v} R)} (f : X ⟶ Y) :
    homotopyEquivalences R f ↔
      AddCommGrp.underlying.homotopyEquivalences
        (Functor.whiskerRight f (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v})) := sorry

namespace homotopyEquivalences

namespace alternatingFace

/-- An underlying simplicial-set homotopy equivalence of simplicial modules induces an
alternating-face quasi-isomorphism. -/
@[stacks 08P2 "alternating-face quasi-isomorphisms of simplicial modules"]
theorem le_quasiIso (R : Type u) [Ring R] :
    ModuleCat.underlying.homotopyEquivalences R ≤
      (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.down ℕ)).inverseImage
        (alternatingFaceMapComplex (ModuleCat.{v} R)) := sorry

end alternatingFace

namespace normalizedMoore

/-- An underlying simplicial-set homotopy equivalence of simplicial modules induces a
normalized-Moore quasi-isomorphism. -/
@[stacks 08P2 "normalized-Moore quasi-isomorphisms of simplicial modules"]
theorem le_quasiIso (R : Type u) [Ring R] :
    ModuleCat.underlying.homotopyEquivalences R ≤
      (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex (ModuleCat.{v} R)) := sorry

end normalizedMoore

end homotopyEquivalences

end CategoryTheory.SimplicialObject.ModuleCat.underlying
