/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Frobenius
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.Sheaf

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}} (p : ℕ) [Fact p.Prime] [S.IsCharP p]
variable (E : S.Modules) [SheafOfModules.IsFiniteLocallyFree E]
variable (F : Frobenius.smallEtaleAbelian S E ⟶ Frobenius.smallEtaleAbelian S E)

/- Lemma 63.13.1 (1): the cokernel of `F - 𝟙` vanishes for a Frobenius-semilinear
endomorphism of a finite locally free module on `S_étale`. -/
@[stacks 0GKU] #check
  (AlgebraicGeometry.Scheme.Etale.Frobenius.isZero_cokernel_sub_id p E F :
    Frobenius.IsFrobeniusSemilinear p E F → IsZero (cokernel (F - 𝟙 _)))

/- Lemma 63.13.1 (2): the kernel of `F - 𝟙` is a constructible abelian sheaf on
`S_étale`. -/
@[stacks 0GKU] #check
  (AlgebraicGeometry.Scheme.Etale.Frobenius.isConstructibleEtale_kernel_sub_id p E F :
    Frobenius.IsFrobeniusSemilinear p E F →
      IsConstructibleEtale
        (fun {Y} f ↦ ((Scheme.smallEtalePullback f).sheafPullback AddCommGrpCat.{u}
          S.smallEtaleTopology Y.smallEtaleTopology).obj)
        (fun {Y} G ↦ IsFiniteLocallyConstantAddCommGrp G)
        (kernel (F - 𝟙 _)))

end AlgebraicGeometry.Scheme.Etale
