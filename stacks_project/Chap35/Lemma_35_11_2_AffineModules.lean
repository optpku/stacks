/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.SmallAffine

/-!
# Small affine Zariski and étale sites

This source bridge reexports the uniform small affine site API.
-/

universe u

#check
  (AlgebraicGeometry.SmallStandardTopology.Affine.site :
    ∀ (_ : AlgebraicGeometry.SmallStandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
      CategoryTheory.Cat.{u, u + 1})
