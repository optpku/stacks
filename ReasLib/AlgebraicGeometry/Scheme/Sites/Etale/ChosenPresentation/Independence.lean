/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.SmallAffineComparison
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.Small
public import Mathlib.CategoryTheory.Sites.Equivalence

@[expose] public section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigEtaleSite

/-- The small étale sheaf categories associated to two chosen big étale-site
presentations representing the same scheme are equivalent. -/
theorem smallToposIndependent
    (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (Y : ChosenBigEtaleSite.{u, w})
    (SX : X.carrier) (SY : Y.carrier)
    (hX : X.toScheme.obj SX = S) (hY : Y.toScheme.obj SY = S) :
    Nonempty
      (Sheaf (smallTopology X SX) (Type (max u (max v w))) ≌
        Sheaf (smallTopology Y SY) (Type (max u (max v w)))) := sorry

end AlgebraicGeometry.ChosenBigEtaleSite
