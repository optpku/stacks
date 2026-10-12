/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CotangentComplex
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 92.24.1: Let `f : X ⟶ Y` be a morphism of schemes. The cotangent
complex `L_{X/Y}` of `X` over `Y` is the cotangent complex of `f` as a morphism
of ringed spaces (Definition 92.20.1). -/
@[stacks 08T2]
#check (AlgebraicGeometry.Scheme.Hom.cotangentComplex :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (X ⟶ Y) → CochainComplex X.Modules ℤ)
