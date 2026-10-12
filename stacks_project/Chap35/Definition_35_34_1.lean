/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData
import StacksCheckRecall

open CategoryTheory

universe u v

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

/- Definition 35.34.1: the category of descent data relative to a scheme morphism
`f : X ⟶ S`. Its specialization to `PUnit.{v + 1}` is canonical, while `Chosen` exposes
the textbook presentation using chosen pullbacks. -/
@[stacks 023V] #check
  (AlgebraicGeometry.Scheme.DescentData
      (I := PUnit.{v + 1}) (S := S) (fun _ ↦ X) (fun _ ↦ f) :
    Type (max (max v (u + 1)) u))

#check @AlgebraicGeometry.Scheme.DescentData.Chosen
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.ofIso
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.iso
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.cocycle
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.hom_comm
#check @AlgebraicGeometry.Scheme.DescentData.Chosen.equivalence
