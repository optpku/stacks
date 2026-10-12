/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Blowup.Pullback
import StacksCheckRecall

universe u

/- Lemma 31.32.11 (1): the pullback of every effective Cartier divisor along a blowup morphism
is defined. -/
@[stacks 0809] #check
  (AlgebraicGeometry.Blowup.pullbackDefined :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I) (D : X.IdealSheafData)
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι],
      AlgebraicGeometry.Scheme.IdealSheafData.pullbackDefined D π.hom)

/- Lemma 31.32.11 (2): pullbacks of regular meromorphic functions are defined along a blowup
morphism. -/
@[stacks 0809] #check
  (AlgebraicGeometry.Blowup.pullbacksRegularMeromorphicFunctionsDefined :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} {I : X.IdealSheafData}
      (π : AlgebraicGeometry.Blowup X I),
      AlgebraicGeometry.LocallyRingedSpace.Hom.pullbacksRegularMeromorphicFunctionsDefined
        π.hom.toLRSHom)
