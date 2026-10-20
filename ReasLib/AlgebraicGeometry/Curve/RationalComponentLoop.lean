/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Logic.Equiv.Fin.Rotate
public import ReasLib.AlgebraicGeometry.Curve.RationalCycle

/-!
# Rational-component loops in nodal curves
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- An irreducible component of a scheme over a field, viewed as a scheme over `k`. -/
def irreducibleComponentOver {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) : SchemeOverField k :=
  Over.mk (X.left.irreducibleComponentSubschemeι Z ≫ X.hom)

/-- The structure morphism of `irreducibleComponentOver X Z` is the component
immersion followed by the structure morphism of `X`. -/
theorem irreducibleComponentOver_hom {k : Type u} [Field k] (X : SchemeOverField k)
    (Z : irreducibleComponents X.left) :
    (irreducibleComponentOver X Z).hom =
      X.left.irreducibleComponentSubschemeι Z ≫ X.hom := rfl

/-- An at-worst-nodal curve over `k` with smooth irreducible components whose dual
graph contains a cycle of at least two distinct rational curves. The cycle need not include every
irreducible component, and components off the cycle need not be rational. -/
def IsNodalWithRationalComponentLoop {k : Type u} [Field k]
    (X : SchemeOverField k) : Prop :=
  SchemeOverField.atWorstNodal X ∧
    (∀ Z : irreducibleComponents X.left, Smooth (irreducibleComponentOver X Z).hom) ∧
    ∃ (n : ℕ) (hn : 2 ≤ n) (C : Fin n → irreducibleComponents X.left)
      (node : Fin n → X.left),
      Function.Injective C ∧ Function.Injective node ∧
        (∀ i, Nonempty (RationalCurve k (irreducibleComponentOver X (C i)))) ∧
        (∀ i, node i ∈ (C i : Set X.left)) ∧
        (∀ i, node i ∈ (C (finRotate n i) : Set X.left)) ∧
        (∀ i, SchemeOverField.isNode X (node i))

/-- A curve has a rational-component loop exactly when it is at worst nodal, all its
components are smooth, and distinct rational components and nodes form a cycle
of length at least two. -/
theorem IsNodalWithRationalComponentLoop_iff {k : Type u} [Field k]
    (X : SchemeOverField k) :
    IsNodalWithRationalComponentLoop X ↔
      SchemeOverField.atWorstNodal X ∧
        (∀ Z : irreducibleComponents X.left,
          Smooth (irreducibleComponentOver X Z).hom) ∧
        ∃ (n : ℕ) (hn : 2 ≤ n) (C : Fin n → irreducibleComponents X.left)
          (node : Fin n → X.left),
          Function.Injective C ∧ Function.Injective node ∧
            (∀ i, Nonempty (RationalCurve k (irreducibleComponentOver X (C i)))) ∧
            (∀ i, node i ∈ (C i : Set X.left)) ∧
            (∀ i, node i ∈ (C (finRotate n i) : Set X.left)) ∧
            (∀ i, SchemeOverField.isNode X (node i)) := Iff.rfl

end AlgebraicGeometry.Scheme.Hom
