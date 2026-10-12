/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Associated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

universe u

/- 27.10.1.5: For every `n : ℤ`, there is a comparison morphism
`M̃ ⊗ 𝒪_X(n) ⟶ (M(n))̃`. -/
@[stacks 01MQ] #check
  (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.canonicalHom :
    ∀ {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
      [DirectSum.Decomposition ℳ] (n : ℤ),
      (tensorObj
          (AlgebraicGeometry.Proj.AssociatedModule.sheaf 𝒜 ℳ)
          (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf
            (R := ℤ) (A := A) 𝒜 n) :
        (AlgebraicGeometry.Proj 𝒜).Modules) ⟶
      AlgebraicGeometry.Proj.AssociatedModule.sheaf 𝒜
        (GradedModule.shiftGrading ℳ n))

end
