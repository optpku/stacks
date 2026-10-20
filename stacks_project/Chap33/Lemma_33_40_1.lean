/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Normalization.Branch

@[expose] public section

open scoped BigOperators

universe u v

/- Lemma 33.40.1 (1): Let `X` be a scheme whose quasi-compact opens have
finitely many irreducible components. The number of branches of `X` at `x` is
the number of inverse images of `x` in the normalization of `X`. -/
@[stacks 0C1S] #check
  (AlgebraicGeometry.Scheme.Normalization.branchNumberAt_eq_fiberCard :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (x : X) (Ah : Type v) [CommRing Ah] [Algebra (X.presheaf.stalk x) Ah]
      [IsHenselizationOf (X.presheaf.stalk x) Ah],
      X.branchNumberAt x Ah =
        (Set.univ : Set (X.normalizationTo.pointsOver x)).encard)

/- Lemma 33.40.1 (2): Let `X` be a scheme whose quasi-compact opens have
finitely many irreducible components. The number of geometric branches of `X`
at `x` is the sum, over the inverse images of `x` in the normalization, of the
separable residue-field degrees over the residue field of `x`. -/
@[stacks 0C1S] #check
  (AlgebraicGeometry.Scheme.Normalization.geometricBranchNumberAt_eq_tsumSepDegree :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.Scheme.HasFiniteIrreducibleComponentsOnCompactOpens X]
      (x : X) (Ash : Type v) [CommRing Ash] [Algebra (X.presheaf.stalk x) Ash]
      [IsStrictHenselizationOf (X.presheaf.stalk x) Ash],
      X.geometricBranchNumberAt x Ash =
        ∑' xnu : X.normalizationTo.pointsOver x,
          (Field.finSepDegree (X.residueField x)
            (X.normalization.residueField xnu) : ℕ∞))
