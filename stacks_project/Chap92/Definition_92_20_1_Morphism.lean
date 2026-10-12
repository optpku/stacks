/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.NaiveCotangent

/-!
# Cotangent complexes of morphisms of ringed spaces

This leaf provides the source-facing compatibility surface for the cotangent complexes of
morphisms of ringed spaces.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

#check (AlgebraicGeometry.RingedSpace.cotangentComplex :
  ∀ {X S : AlgebraicGeometry.RingedSpace.{u}},
    (X ⟶ S) → CochainComplex X.Modules ℤ)
