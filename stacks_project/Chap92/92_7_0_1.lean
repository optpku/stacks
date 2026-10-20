module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
import StacksCheckRecall

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

variable (A B C : Type u)
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

/- 92.7.0.1: for a sequence of ring maps A → B → C, the transitivity triangle
in D(C) is distinguished and has the form
tensor A B C ⟶ derived A C ⟶ derived B C ⟶ (tensor A B C)⟦1⟧. -/
@[stacks 08QS]
#check (Algebra.CotangentComplex.transitivityTriangle_distinguished A B C :
  Algebra.CotangentComplex.transitivityTriangle A B C ∈
    distTriang (DerivedCategory (ModuleCat.{u} C)))

#check (Algebra.CotangentComplex.transitivityTriangle A B C :
  Triangle (DerivedCategory (ModuleCat.{u} C)))
#check (Algebra.CotangentComplex.tensorDerivedIso A B C :
  tensorDerived A B C ≅ tensor A B C)

#check (tensorMap A B C : tensor A B C ⟶ derived A C)
#check (toRelativeMap A B C : derived A C ⟶ derived B C)
#check (connectingMap A B C : derived B C ⟶ (tensor A B C)⟦(1 : ℤ)⟧)
#check (Algebra.CotangentComplex.transitivityTriangle_obj₁ A B C :
  (transitivityTriangle A B C).obj₁ = tensor A B C)
#check (Algebra.CotangentComplex.transitivityTriangle_obj₂ A B C :
  (transitivityTriangle A B C).obj₂ = derived A C)
#check (Algebra.CotangentComplex.transitivityTriangle_obj₃ A B C :
  (transitivityTriangle A B C).obj₃ = derived B C)
#check (Algebra.CotangentComplex.transitivityTriangle_mor₁ A B C :
  (transitivityTriangle A B C).mor₁ = tensorMap A B C)
#check (Algebra.CotangentComplex.transitivityTriangle_mor₂ A B C :
  (transitivityTriangle A B C).mor₂ = toRelativeMap A B C)
#check (Algebra.CotangentComplex.transitivityTriangle_mor₃ A B C :
  (transitivityTriangle A B C).mor₃ = connectingMap A B C)
