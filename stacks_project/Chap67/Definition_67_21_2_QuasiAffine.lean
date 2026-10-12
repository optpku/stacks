/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiAffine

@[expose] public section

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.QuasiAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      {X Y : AlgebraicGeometry.AlgebraicSpace S}, (X ⟶ Y) → Prop)
