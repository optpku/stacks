/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.StandardProetale

@[expose] public section

universe u

#check
  (AlgebraicGeometry.StandardProetaleCover :
    ∀ (T : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsAffine T], Type (u + 1))
