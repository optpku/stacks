module

public import stacks_project.Chap78.Definition_78_12_1
public import stacks_project.Chap78.Lemma_78_15_1_Action
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory
open GroupoidAlgebraicSpace

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  (X : GroupAlgebraicSpace.Action G)

/- Definition 78.10.1: The objects of `System (ofAction G X)` are pairs `(F, α)`
with `F` a quasi-coherent module on `X` and a linearization
`α : actionTarget`-pullback of `F` ⟶ `actionSource`-pullback of `F` satisfying
the cocycle and unit laws. Here `actionTarget` is `a : G ×_B X ⟶ X` and
`actionSource` is `pr₁ : G ×_B X ⟶ X`. -/
@[stacks 043T] #check (System (ofAction G X))

/- Companion: equivariant quasi-coherent modules are built from a quasi-coherent
module, a linearization, and the cocycle and unit laws. -/
#check System.of

/- Companion: `obj` and `action` recover the underlying module and its
linearization. -/
#check System.obj
#check System.action

/- Companion: `spec` packages the cocycle and unit laws. -/
#check System.spec

/- Companion: `actionTarget` is `a : G ×_B X ⟶ X` and `actionSource` is
`pr₁ : G ×_B X ⟶ X`. -/
#check actionTarget
#check actionSource

/- Companion: `Cocycle` and `Unit` are the two laws on `(F, α)`. -/
#check Cocycle
#check Unit
