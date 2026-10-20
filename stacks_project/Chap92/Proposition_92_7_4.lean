module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

/- Proposition 92.7.4. Let A → B → C be ring maps. There is a canonical distinguished
triangle
tensor A B C ⟶ derived A C ⟶ derived B C ⟶ (tensor A B C)⟦1⟧
in D(C). -/
@[stacks 08QX]
#check (Algebra.CotangentComplex.transitivityTriangle_distinguished :
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    Algebra.CotangentComplex.transitivityTriangle A B C ∈
      distTriang
        (DerivedCategory (ModuleCat.{u} C)))

variable (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]

#check (Algebra.CotangentComplex.transitivityTriangle A B C :
  Triangle (DerivedCategory (ModuleCat.{u} C)))
#check (Algebra.CotangentComplex.tensorMap A B C :
  Algebra.CotangentComplex.tensor A B C ⟶ Algebra.CotangentComplex.derived A C)
#check (Algebra.CotangentComplex.toRelativeMap A B C :
  Algebra.CotangentComplex.derived A C ⟶ Algebra.CotangentComplex.derived B C)
#check (Algebra.CotangentComplex.connectingMap A B C :
  Algebra.CotangentComplex.derived B C ⟶
    (Algebra.CotangentComplex.tensor A B C)⟦(1 : ℤ)⟧)

/- The canonical comparison identifies the first vertex with derived scalar extension. -/
#check (Algebra.CotangentComplex.tensorDerivedIso A B C :
  Algebra.CotangentComplex.tensorDerived A B C ≅ Algebra.CotangentComplex.tensor A B C)

