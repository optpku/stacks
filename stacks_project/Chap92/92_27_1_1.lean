/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.«92_27_1_1_Morphism»
public import stacks_project.Chap92.«92_27_1_1_Object»
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.AlgebraicSpace.Cotangent

/- 92.27.1.1 (1): the morphism of ringed topoi i : (Sh(C_{X/Λ}), underline{𝒪}_X) ⟶
(Sh(C_{X/Λ}), O) is the identity on underlying topoi, with i♯ : O ⟶ underline{𝒪}_X
the obvious map. -/
@[stacks 08VK]
#check AlgebraicGeometry.AlgebraicSpace.Cotangent.i

/- 92.27.1.1 (2): the morphism of ringed topoi π : (Sh(C_{X/Λ}), underline{𝒪}_X) ⟶
(Sh(X_étale), 𝒪_X) is the forgetful projection along u : C_{X/Λ} ⥤ X_étale. -/
@[stacks 08VK]
#check AlgebraicGeometry.AlgebraicSpace.Cotangent.π
