/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Syntomic.StandardAffine
import StacksCheckRecall

@[expose] public section

universe u

/-!
# Definition 34.6.8

The canonical syntomic topology on `Over S`, its affine restriction, and the
separate standard-affine syntomic presentation are reusable scheme-site
infrastructure.  They are recalled directly from their neutral owners.
-/

#check (AlgebraicGeometry.Scheme.syntomicOverTopology :
  (S : AlgebraicGeometry.Scheme.{u}) →
    CategoryTheory.GrothendieckTopology (CategoryTheory.Over S))

#check (AlgebraicGeometry.Scheme.AffineOver :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check (AlgebraicGeometry.Scheme.Syntomic.StandardAffine.topology :
  (S : AlgebraicGeometry.Scheme.{u}) →
    CategoryTheory.GrothendieckTopology S.AffineOver)

/- Definition 34.6.8: the big affine syntomic site over `S` has affine
`S`-schemes as objects and finite standard syntomic covering families. -/
@[stacks 03X3] #check
  (AlgebraicGeometry.Scheme.Syntomic.StandardAffine.pretopology :
    (S : AlgebraicGeometry.Scheme.{u}) → CategoryTheory.Pretopology S.AffineOver)
