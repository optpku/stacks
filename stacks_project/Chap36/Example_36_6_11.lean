/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.PrincipalOpen.FractionClass
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace ModuleCech.LocalCohomology

variable (R : CommRingCat.{u}) (c : ℕ) (f : Fin c → R) (M : ModuleCat R)

/- Example 36.6.11: For an affine scheme `Spec R` and the module sheaf
`AlgebraicGeometry.tilde M`, the class map attached to `f` sends a quotient class to
its top Čech fraction class. -/
@[stacks 0G7R] #check
  (ModuleCech.LocalCohomology.cechClass_π
      (fun i ↦ (Scheme.ΓSpecIso R).inv (f i)) (AlgebraicGeometry.tilde M) :
    let g : Fin c → Γ(Spec R, ⊤) := fun i ↦ (Scheme.ΓSpecIso R).inv (f i)
    let ℱ := AlgebraicGeometry.tilde M
    (quotientProjection g).app ℱ ≫ (cechClass g).app ℱ =
      (numeratorClass g).app ℱ)

end ModuleCech.LocalCohomology

end
