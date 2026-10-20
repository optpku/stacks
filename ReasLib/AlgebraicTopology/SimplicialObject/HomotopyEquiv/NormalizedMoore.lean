/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Homotopy.NormalizedMoore
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
public import ReasLib.Algebra.Homology.Homotopy.Equiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Normalized Moore complexes and simplicial homotopy equivalences

This leaf records that the normalized Moore complex functor sends simplicial
homotopy equivalences to chain-homotopy equivalences in an abelian category.
-/

@[expose] public section

open CategoryTheory
open AlgebraicTopology
open AlgebraicTopology.DoldKan

universe u v

namespace CategoryTheory.SimplicialObject

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {U V : SimplicialObject A} {a : U ⟶ V}

/-- The normalized Moore complex functor preserves the full morphism property of simplicial
homotopy equivalences. -/
@[stacks 019T "normalized-Moore functor preserves homotopy equivalences"]
theorem homotopyEquivalences.normalizedMoore :
    homotopyEquivalences A ≤
      (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ)).inverseImage
        (normalizedMooreComplex A) := sorry

namespace HomotopyEquiv

/-- The normalized Moore complex of a simplicial homotopy equivalence, retaining the image of
its chosen inverse. -/
@[stacks 019T "structured normalized-Moore homotopy equivalence"]
noncomputable def normalizedMoore (e : HomotopyEquiv U V) :
    HomRel.Equiv (homotopic A (ComplexShape.down ℕ))
      ((normalizedMooreComplex A).obj U) ((normalizedMooreComplex A).obj V) :=
  e.map (normalizedMooreComplex A)

namespace normalizedMoore

/-- The forward map of the normalized-Moore image is the normalized-Moore map of the original
forward morphism. -/
@[simp, stacks 019T "normalized-Moore homotopy-equivalence forward map"]
theorem hom (e : HomotopyEquiv U V) :
    e.normalizedMoore.hom = (normalizedMooreComplex A).map e.hom := sorry

/-- The chosen inverse of the normalized-Moore image is the normalized-Moore map of the original
chosen inverse. -/
@[simp, stacks 019T "normalized-Moore homotopy-equivalence inverse map"]
theorem inv (e : HomotopyEquiv U V) :
    e.normalizedMoore.inv = (normalizedMooreComplex A).map e.inv := sorry

/-- A simplicial homotopy equivalence induces a chain-homotopy equivalence on normalized Moore
complexes. -/
@[stacks 019T "normalized-Moore homotopy equivalence"]
theorem isHomotopyEquivalence (e : HomotopyEquiv U V) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((normalizedMooreComplex A).map e.hom) := sorry

end normalizedMoore

end HomotopyEquiv

namespace IsHomotopyEquivalence

/-- A simplicial homotopy-equivalence morphism induces a chain-homotopy equivalence on normalized
Moore complexes. -/
@[stacks 019T "normalized-Moore homotopy-equivalence morphism"]
theorem normalizedMoore (ha : IsHomotopyEquivalence a) :
    (HomologicalComplex.homotopyEquivalences A (ComplexShape.down ℕ))
      ((normalizedMooreComplex A).map a) := sorry

end IsHomotopyEquivalence

end CategoryTheory.SimplicialObject
