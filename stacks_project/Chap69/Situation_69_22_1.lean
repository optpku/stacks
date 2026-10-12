/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Spec
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap69.Definition_69_12_1_Instances
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
variable (X : AlgebraicSpace (Spec (CommRingCat.of A)))
variable (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
variable (F : X.Modules) [F.IsCoherent]

/- Situation 69.22.1 (1): `A` is a Noetherian ring. -/
@[stacks 08AV] #check (inferInstance : IsNoetherianRing A)

/- Situation 69.22.1 (2): `I ⊂ A` is an ideal. -/
@[stacks 08AV] #check (I : Ideal A)

/- Situation 69.22.1 (3): `f : X ⟶ Spec(A)` is a proper morphism of algebraic spaces. -/
@[stacks 08AV] #check (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))
@[stacks 08AV] #check (inferInstance : Proper f)

/- Situation 69.22.1 (4): `F` is a coherent sheaf on `X`. -/
@[stacks 08AV] #check (inferInstance : F.IsCoherent)

end
