module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Ideal.Torsion
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace AlgebraicGeometry.AlgebraicSpace.Modules
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/- Definition 70.14.3: let `S` be a scheme and `X` an algebraic space over `S`.
If `I ⊂ 𝒪_X` is a quasi-coherent sheaf of ideals of finite type and `ℱ` is a
quasi-coherent `𝒪_X`-module, then the quasi-coherent subsheaf
`idealTorsionSubsheaf I ℱ ⊂ ℱ` constructed in Lemma 70.14.2 is called the
subsheaf of sections annihilated by `I`. -/
@[stacks 0857]
#check (AlgebraicGeometry.AlgebraicSpace.Modules.idealTorsionSubsheaf :
  IdealSubobject X → X.Modules → X.Modules)

/- The named subsheaf includes canonically into `ℱ`. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.idealTorsionSubsheafι :
  ∀ (I : IdealSubobject X) (ℱ : X.Modules), idealTorsionSubsheaf I ℱ ⟶ ℱ)

/- If `I` is a quasi-coherent finite type ideal sheaf and `ℱ` is quasi-coherent,
then the subsheaf of sections annihilated by `I` is quasi-coherent. -/
#check (AlgebraicGeometry.AlgebraicSpace.Modules.idealTorsionSubsheaf_isQuasicoherent :
  ∀ (I : IdealSubobject X) (ℱ : X.Modules),
    [(I : X.Modules).IsQuasicoherent] → [(I : X.Modules).IsFiniteType] →
    [ℱ.IsQuasicoherent] → (idealTorsionSubsheaf I ℱ).IsQuasicoherent)

end AlgebraicGeometry.AlgebraicSpace.Modules
