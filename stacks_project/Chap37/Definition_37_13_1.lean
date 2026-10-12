/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

/- Definition 37.13.1: for a morphism of schemes `f : X ⟶ Y`, the naive cotangent complex,
denoted `NL_f` or `NL_{X/Y}`, is represented by `f.naiveCotangent` and is definitionally
`NL[f.toShHom]`. -/
@[stacks 0D0H] #check
  (@AlgebraicGeometry.Scheme.Hom.naiveCotangent :
    {X Y : Scheme.{u}} → (X ⟶ Y) → CochainComplex X.Modules ℤ)
