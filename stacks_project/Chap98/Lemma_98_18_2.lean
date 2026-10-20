module

public import stacks_project.Chap98.Definition_98_18_1
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import ReasLib.AlgebraicGeometry.AlgebraicStack.StrongRimSchlessinger
import StacksCheckRecall

/-!
# Algebraic stacks satisfy the strong Rim-Schlessinger condition

An algebraic stack over a scheme `S` satisfies condition (RS*).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.GroupoidsOver

/- Lemma 98.18.2: if `X` is an algebraic stack over a scheme `S`, then the
category fibred in groupoids `X` satisfies condition (RS*). -/
@[stacks 0CXP]
#check (AlgebraicGeometry.GroupoidsOver.instHasStrongRimSchlessinger_algebraicStack :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X],
    HasStrongRimSchlessinger X)

end AlgebraicGeometry.GroupoidsOver
