/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Abelian

/-! # Homology of quasi-coherent complexes on associated sites -/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits GroupoidsOver

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.QCoh

variable {S : Scheme.{u}}

/-- The canonical functor from quasi-coherent modules to modules on an associated
site preserves zero morphisms. -/
instance toAssociatedModules_preservesZeroMorphisms
    (X : GroupoidsOver S) (τ : StandardTopology) :
    (toAssociatedModules X τ).PreservesZeroMorphisms := sorry

/-- The homology of a short complex of quasi-coherent modules, computed in the
category of modules on the associated `τ`-site. -/
def associatedHomology (X : GroupoidsOver S) (τ : StandardTopology)
    (sc : ShortComplex (QCoh X)) : associatedModules X τ :=
  (sc.map (toAssociatedModules X τ)).homology

/-- Associated homology is the homology of the short complex obtained by applying
the canonical associated-module functor. -/
theorem associatedHomology_eq (X : GroupoidsOver S) (τ : StandardTopology)
    (sc : ShortComplex (QCoh X)) :
    associatedHomology X τ sc = (sc.map (toAssociatedModules X τ)).homology := rfl

end AlgebraicGeometry.GroupoidsOver.QCoh
