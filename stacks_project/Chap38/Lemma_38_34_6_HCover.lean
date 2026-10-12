/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Cover.H.Comparison

universe u v

#check
  (AlgebraicGeometry.Scheme.HCovering :
    ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v},
      (ι → CategoryTheory.Over T) → Prop)
