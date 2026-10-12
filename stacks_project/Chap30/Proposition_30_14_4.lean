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

/- Proposition 30.14.4: when `A` is finite type over its Noetherian degree-zero part and
generated in degree one, the quotient of finite graded modules by torsion modules is equivalent
to coherent modules on `Proj 𝒜`. -/
@[stacks 0BXD] #check
  (AlgebraicGeometry.Proj.Associated.Torsion.isQuasiInverse :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
      (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1),
      (AlgebraicGeometry.Proj.Associated.Torsion.quotientFunctor 𝒜 hgenerated).IsQuasiInverse
        (AlgebraicGeometry.Proj.Associated.Torsion.quasiInverse 𝒜))

#check
  (AlgebraicGeometry.Proj.Associated.Torsion.quasiInverse :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)],
      RingedSpace.Coh (AlgebraicGeometry.Proj 𝒜).toRingedSpace ⥤
        AlgebraicGeometry.Proj.Associated.Torsion.Quotient 𝒜)

#check
  (AlgebraicGeometry.Proj.Associated.Torsion.isEquivalence :
    ∀ {A : Type u} [CommRing A] (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [Algebra.FiniteType (𝒜 0) A] [IsNoetherianRing (𝒜 0)]
      (hgenerated : GradedAlgebra.GeneratedBy 𝒜 1),
      (AlgebraicGeometry.Proj.Associated.Torsion.quotientFunctor 𝒜 hgenerated).IsEquivalence)
