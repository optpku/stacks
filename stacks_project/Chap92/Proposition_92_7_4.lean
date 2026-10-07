module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
import StacksCheckRecall

open Algebra.CotangentComplex
open CategoryTheory
open CategoryTheory.Pretriangulated

/- Proposition 92.7.4. Let A → B → C be ring maps. There is a canonical distinguished
triangle
tensor A B C ⟶ derived A C ⟶ derived B C ⟶ (tensor A B C)⟦1⟧
in D(C). -/
@[stacks 08QX]
#check transitivityTriangle_distinguished

#check transitivityTriangle
#check tensorMap
#check toRelativeMap
#check connectingMap
