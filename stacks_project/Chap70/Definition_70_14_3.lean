/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_14_2_Torsion
public import stacks_project.Chap70.Lemma_70_14_2
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable (I : IdealSubobject X) (ℱ : X.Modules)
variable [(I : X.Modules).IsQuasicoherent] [(I : X.Modules).IsFiniteType]
variable [ℱ.IsQuasicoherent]

/- Definition 70.14.3: let `S` be a scheme and `X` an algebraic space over `S`.
If `I ⊂ 𝒪_X` is a quasi-coherent sheaf of ideals of finite type and `ℱ` is a
quasi-coherent `𝒪_X`-module, then the quasi-coherent subsheaf
`idealTorsionSubsheaf I ℱ ⊂ ℱ` constructed in Lemma 70.14.2 is called the
subsheaf of sections annihilated by `I`. -/
@[stacks 0857]
#check (idealTorsionSubsheaf I ℱ : X.Modules)

/- The named subsheaf includes canonically into `ℱ`. -/
#check (idealTorsionSubsheafι I ℱ : idealTorsionSubsheaf I ℱ ⟶ ℱ)

/- If `I` is a quasi-coherent finite type ideal sheaf and `ℱ` is quasi-coherent,
then the subsheaf of sections annihilated by `I` is quasi-coherent. -/
#check (idealTorsionSubsheaf_isQuasicoherent I ℱ :
  (idealTorsionSubsheaf I ℱ).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
