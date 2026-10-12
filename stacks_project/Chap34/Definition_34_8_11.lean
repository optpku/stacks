/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Basic
import StacksCheckRecall

@[expose] public section

universe u v

/-!
# Definition 34.8.11

This chapter entry records the canonical big `ph` site, its affine restriction,
and the finite affine covering families.
-/

/- Definition 34.8.11: The big affine `ph` site over `S` has affine
`S`-schemes as objects and finite `ph` covering families. -/
@[stacks 0DBL] #check
  (AlgebraicGeometry.Scheme.bigAffinePhPretopology.{u} :
    (S : AlgebraicGeometry.Scheme.{u}) →
      CategoryTheory.Pretopology S.AffineOver)

#check
  (AlgebraicGeometry.Scheme.bigPhSite :
    (S : AlgebraicGeometry.Scheme.{u}) →
      CategoryTheory.GrothendieckTopology (CategoryTheory.Over S))

#check AlgebraicGeometry.Scheme.AffineOver
#check AlgebraicGeometry.Scheme.bigAffinePhPrecoverage
#check AlgebraicGeometry.Scheme.mem_bigAffinePhPrecoverage_iff
#check AlgebraicGeometry.Scheme.ofArrows_mem_bigAffinePhPrecoverage_iff
#check AlgebraicGeometry.Scheme.bigAffinePhTopology
