/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Affine
public import ReasLib.CategoryTheory.Sites.PrecoverageSite

/-!
# Site axioms for chosen pro-étale carriers

The selected covering families on the weakly étale slice and the finite
standard covering families on the affine slice satisfy the site axioms.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- The chosen small pro-étale precoverage satisfies the site axioms. -/
theorem smallPrecoverage.isSite (X : ChosenBigProetaleSite.{u, v})
    (S : X.carrier) : (smallPrecoverage X S).IsSite := sorry

/-- The chosen big affine standard pro-étale precoverage satisfies the site axioms. -/
theorem bigAffineStandardPrecoverage.isSite
    (X : ChosenBigProetaleSite.{u, v}) (S : X.carrier) :
    (bigAffineStandardPrecoverage X S).IsSite := sorry

end AlgebraicGeometry.ChosenBigProetaleSite
