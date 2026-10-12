/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap71.Definition_71_18_1_StrictTransform
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

variable {S : Scheme.{u}} {B B' X : AlgebraicSpace S}
variable (Z : ClosedSubspace B) (b : B' ⟶ B) (f : X ⟶ B)
variable (F : X.Modules) [F.IsQuasicoherent]

/- Definition 71.18.1 (1): given a quasi-coherent 𝒪_X-module F, the strict transform of F
with respect to the blowup of B in Z is the quotient of pr_X^* F by the submodule of
sections supported on |pr_{B'}⁻¹ E|, where E = b⁻¹ Z. -/
@[stacks 0862] #check
  (strictTransformModule b (Z.inverseImage b) f F :
    (strictTransformAmbient b f).Modules)

section
variable [QuasiCompact (strictTransformOpenComplement b (Z.inverseImage b) f).ι]

/- Definition 71.18.1 (2): the strict transform of X is the closed subspace
X' ⊂ X ×_B B' cut out by the quasi-coherent ideal of sections of 𝒪_{X ×_B B'}
supported on |pr_{B'}⁻¹ E|, where E = b⁻¹ Z. -/
@[stacks 0862] #check
  (strictTransform b (Z.inverseImage b) f :
    ClosedSubspace (strictTransformAmbient b f))

end
