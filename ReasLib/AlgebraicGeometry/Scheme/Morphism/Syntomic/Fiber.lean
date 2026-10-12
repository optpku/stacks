/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.AtPoint
public import ReasLib.AlgebraicGeometry.Scheme.OverField.CompleteIntersection

/-!
# Syntomic morphisms and fibers

This module gives a fiberwise criterion for a flat, locally finitely presented
scheme morphism to be syntomic.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Syntomic

variable {X S : Scheme.{u}}

/-- A flat, locally finitely presented scheme morphism whose residue-field fibers are syntomic
is syntomic. -/
theorem of_syntomic_fiberToSpecResidueField
    (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (h : ∀ s : S, Syntomic (f.fiberToSpecResidueField s)) :
    Syntomic f := sorry

end AlgebraicGeometry.Syntomic
