/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiAffine.Ample
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 28.27.1: a scheme `X` is quasi-affine if and only if its structure sheaf
`𝒪_X` is ample. -/
@[stacks 01QE] #check
  (AlgebraicGeometry.Scheme.isQuasiAffine_iff_structureSheaf_isAmple :
    ∀ (X : Scheme.{u}),
      X.IsQuasiAffine ↔
        Scheme.Modules.isAmpleObject (SheafOfModules.unit X.ringCatSheaf))
