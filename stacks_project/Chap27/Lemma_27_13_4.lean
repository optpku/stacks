/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.MorphismProperties
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.UniversallyClosed
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 27.13.4: for every scheme `S` and natural number `n`, the canonical projection
`ProjectiveSpace.toBase n S` is separated, quasi-compact, satisfies the existence and uniqueness
parts of the valuative criterion, and is universally closed. -/
@[stacks 01NH] #check
  (AlgebraicGeometry.ProjectiveSpace.toBase_isSeparated :
    ∀ (n : ℕ) (S : AlgebraicGeometry.Scheme.{u}),
      AlgebraicGeometry.IsSeparated
        (AlgebraicGeometry.ProjectiveSpace.toBase n S))

variable (n : ℕ) (S : AlgebraicGeometry.Scheme.{u})

#check
  (AlgebraicGeometry.instQuasiCompactOfUniversallyClosed
      (f := AlgebraicGeometry.ProjectiveSpace.toBase n S) :
    AlgebraicGeometry.QuasiCompact
      (AlgebraicGeometry.ProjectiveSpace.toBase n S))

#check
  (AlgebraicGeometry.UniversallyClosed.valuativeCriterion
      (AlgebraicGeometry.ProjectiveSpace.toBase n S) :
    AlgebraicGeometry.ValuativeCriterion.Existence
      (AlgebraicGeometry.ProjectiveSpace.toBase n S))

#check
  (AlgebraicGeometry.IsSeparated.valuativeCriterion
      (AlgebraicGeometry.ProjectiveSpace.toBase n S) :
    AlgebraicGeometry.ValuativeCriterion.Uniqueness
      (AlgebraicGeometry.ProjectiveSpace.toBase n S))

#check
  (AlgebraicGeometry.ProjectiveSpace.toBase_universallyClosed n S :
    AlgebraicGeometry.UniversallyClosed
      (AlgebraicGeometry.ProjectiveSpace.toBase n S))
