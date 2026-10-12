/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth.Restriction

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

#check (@AlgebraicGeometry.FormallySmooth.resLE :
  ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (e : U ≤ f ⁻¹ᵁ V) [AlgebraicGeometry.FormallySmooth f],
      AlgebraicGeometry.FormallySmooth (f.resLE V U e))
