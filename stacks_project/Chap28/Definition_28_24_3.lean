/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Torsion
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

variable (I : X.IdealSheafData) (ℱ : X.Modules)
variable [ℱ.IsQuasicoherent]
variable [((Subobject.underlying.obj I.toSubobject : X.Modules).IsFiniteType)]

/- Definition 28.24.3: for a finite-type quasi-coherent ideal sheaf `I` on a scheme `X` and a
quasi-coherent module sheaf `ℱ`, this is the subsheaf of sections annihilated by `I`. -/
@[stacks 01PP] #check (AlgebraicGeometry.Scheme.Modules.idealTorsionSubsheaf I ℱ : X.Modules)

/- The canonical inclusion of the subsheaf of sections annihilated by `I` into `ℱ`. -/
#check (AlgebraicGeometry.Scheme.Modules.idealTorsionSubsheafι I ℱ :
  AlgebraicGeometry.Scheme.Modules.idealTorsionSubsheaf I ℱ ⟶ ℱ)

end AlgebraicGeometry.Scheme.Modules
