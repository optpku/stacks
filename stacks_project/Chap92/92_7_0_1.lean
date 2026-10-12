/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
import StacksCheckRecall

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

variable (A B C : Type u)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- 92.7.0.1: for a sequence of ring maps A → B → C, the transitivity triangle
in D(C) is
tensor A B C ⟶ derived A C ⟶ derived B C ⟶ (tensor A B C)⟦1⟧. -/
@[stacks 08QS]
#check (transitivityTriangle A B C : Triangle (DerivedCategory (ModuleCat.{u} C)))

#check (tensorMap A B C : tensor A B C ⟶ derived A C)
#check (toRelativeMap A B C : derived A C ⟶ derived B C)
#check (connectingMap A B C : derived B C ⟶ (tensor A B C)⟦(1 : ℤ)⟧)
#check transitivityTriangle_obj₁ A B C
#check transitivityTriangle_obj₂ A B C
#check transitivityTriangle_obj₃ A B C
#check transitivityTriangle_mor₁ A B C
#check transitivityTriangle_mor₂ A B C
#check transitivityTriangle_mor₃ A B C
