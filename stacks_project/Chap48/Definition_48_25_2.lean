/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Definition 48.25.2 (1): a scheme morphism is Gorenstein at `x` if it is flat at
`x` and the local ring of the fibre over `f x` at `f.asFiber x` is Gorenstein. -/
@[stacks 0C04] #check
  (AlgebraicGeometry.Scheme.Hom.gorensteinAt :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → X → Prop)

/- Definition 48.25.2 (2): a scheme morphism with locally Noetherian fibres is
Gorenstein if it is Gorenstein at every source point. -/
@[stacks 0C04] #check
  (AlgebraicGeometry.Gorenstein :
    {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)

#check AlgebraicGeometry.Scheme.Hom.gorensteinAt_iff
#check AlgebraicGeometry.gorenstein_iff
#check AlgebraicGeometry.gorenstein_iff_forall_gorensteinAt
