/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.SerreQuotient
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

/- Proposition 30.15.3: for a Noetherian graded ring `A`, the quotient of finitely generated
graded `A`-modules by irrelevant modules is equivalent to coherent modules on `Proj 𝒜`. -/
@[stacks 0BXF] #check
  (AlgebraicGeometry.Proj.Associated.Irrelevant.isEquivalence :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [IsNoetherianRing A],
      (AlgebraicGeometry.Proj.Associated.Irrelevant.quotientFunctor 𝒜).IsEquivalence)

#check
  (AlgebraicGeometry.Proj.Associated.Irrelevant.quasiInverse :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [IsNoetherianRing A],
      RingedSpace.Coh (AlgebraicGeometry.Proj 𝒜).toRingedSpace ⥤
        (AlgebraicGeometry.Proj.Associated.irrelevant 𝒜).isoModSerre.Localization)

#check
  (AlgebraicGeometry.Proj.Associated.Irrelevant.isQuasiInverse :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [IsNoetherianRing A],
      (AlgebraicGeometry.Proj.Associated.Irrelevant.quotientFunctor 𝒜).IsQuasiInverse
        (AlgebraicGeometry.Proj.Associated.Irrelevant.quasiInverse 𝒜))
