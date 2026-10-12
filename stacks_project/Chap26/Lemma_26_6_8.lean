/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.GlobalSections.Affine
public import ReasLib.AlgebraicGeometry.Scheme.AffineOpen.Complement
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.6.8: a locally ringed space covered by two complementary affine restrictions is
canonically affine. -/
@[stacks 01I5] #check LocallyRingedSpace.isIso_toΓSpec_of_isCompl

/- The scheme-level specialization packages the same comparison as an `IsAffine` instance. -/
#check Scheme.isAffine_of_isCompl_of_isAffineOpen
