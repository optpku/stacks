/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification.IsomorphismLocus
import StacksCheckRecall

/-!
# Modifications are isomorphisms over a nonempty open

A modification of integral algebraic spaces is an isomorphism over some
nonempty open subspace of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.8.2: Let `f : X' ⟶ X` be a modification as in Definition 72.8.1.
There exists a nonempty open `U ⊂ X` such that `f⁻¹(U) ⟶ U` is an
isomorphism. -/
@[stacks 0AD9] #check (AlgebraicGeometry.AlgebraicSpace.exists_nonempty_open_isIso_of_isModification :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsModification f],
    ∃ U : OpenSubspace X, U.pointsSet.Nonempty ∧ IsIso (restrictTo f U))

/- The isomorphism locus of a modification of integral algebraic spaces is
nonempty. -/
#check (AlgebraicGeometry.AlgebraicSpace.isomorphismLocus_nonempty_of_isModification :
  ∀ {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsModification f],
    (isomorphismLocus f).Nonempty)

end AlgebraicGeometry.AlgebraicSpace
