/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.GlobalSections.Affine
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

variable (X : LocallyRingedSpace.{u})

/- Definition 26.5.5: an affine locally ringed space is isomorphic to the spectrum of a
commutative ring; its morphisms are the ambient `LocallyRingedSpace.Hom`.  The canonical
`IsAffine` predicate and `AffineScheme` category below are library-level bridges. -/
@[stacks 01HW] #check X.isIso_toΓSpec_iff_exists_isoSpec
#check LocallyRingedSpace.Hom
#check IsAffine
#check AffineScheme

#check X.toΓSpec

/- Constructors and forgetful views of the bundled affine-scheme category. -/
#check AffineScheme.of
#check AffineScheme.forgetToScheme
#check Scheme.isoSpec
