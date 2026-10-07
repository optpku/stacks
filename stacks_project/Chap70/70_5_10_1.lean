module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.CommSq
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

variable {S : Scheme.{u}} {Xi Ui : AlgebraicSpace S} {Ai Bi : CommRingCat.{u}}
variable (σA : Spec Ai ⟶ S) (σB : Spec Bi ⟶ S) (φ : Ai ⟶ Bi)
variable (hσ : Spec.map φ ≫ σA = σB) (cover : Ui ⟶ Xi)
variable (toSpecA : Xi ⟶ ofOver (Over.mk σA))
variable (toSpecB : Ui ⟶ ofOver (Over.mk σB))

/- 70.5.10.1: in `AlgebraicSpace S`, the displayed diagram is the commutative square with
vertices `U_i`, `X_i`, `Spec(B_i)`, `Spec(A_i)`. The top map is the étale cover `U_i ⟶ X_i`,
the left vertical is `U_i ⟶ Spec(B_i)`, the right vertical is `X_i ⟶ Spec(A_i)`, and the
bottom map is `Spec` of `A_i ⟶ B_i`, realized as `ofOverHomMk (Spec.map φ) hσ`. Here `A_i`
is `O_{X_i}(X_i)` and `U_i ⟶ Spec(B_i)` is induced by the chosen sections in the surrounding
07SQ proof; cartesianness is a later deduction, not this displayed equation. -/
@[stacks 084U]
#check CommSq cover toSpecB toSpecA (ofOverHomMk (Spec.map φ) hσ)
