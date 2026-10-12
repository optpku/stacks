/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting

open CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Hom.IsWeighting :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.LocallyQuasiFinite f], (X → ℤ) → Prop)
