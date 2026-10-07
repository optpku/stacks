module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.DegreeOneCover
public import stacks_project.Chap27.Lemma_27_10_2

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry TensorProduct

noncomputable section

universe u

/- Lemma 27.10.3: if the degree-one projective basic opens cover `Proj 𝒜`, then every
canonical twisting sheaf is invertible. -/
@[stacks 01MT] #check
  (AlgebraicGeometry.projTwist_invertible_of_degreeOpen_one_eq_top :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜],
      AlgebraicGeometry.Proj.degreeOpen 𝒜 1 = ⊤ → ∀ n : ℤ,
        AlgebraicGeometry.Scheme.Modules.Invertible
          (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf 𝒜 n))

/- Under the same cover assumption, every standard-open-specified canonical twist
multiplication morphism is an isomorphism. -/
#check
  (AlgebraicGeometry.projTwistMul_isIso_of_degreeOpen_one_eq_top :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (T : AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication 𝒜),
      AlgebraicGeometry.Proj.degreeOpen 𝒜 1 = ⊤ → ∀ a b : ℤ,
        IsIso (T.hom a b))

/- Under the same cover assumption, the induced action of a canonical twist on any module
sheaf is an isomorphism. -/
#check
  (AlgebraicGeometry.projSheafTwistMul_isIso_of_degreeOpen_one_eq_top :
    ∀ {A : Type u} [CommRing A]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      [SymmetricCategory (AlgebraicGeometry.Proj 𝒜).Modules]
      (T : AlgebraicGeometry.Proj.AssociatedModule.TwistMultiplication 𝒜),
      AlgebraicGeometry.Proj.degreeOpen 𝒜 1 = ⊤ →
        ∀ (ℱ : (AlgebraicGeometry.Proj 𝒜).Modules) (a b : ℤ),
          IsIso
            (AlgebraicGeometry.projSheafTwistMul 𝒜
              (AlgebraicGeometry.Proj.AssociatedModule.twistingSheaf 𝒜) T.hom ℱ a b))

/- Under the same cover assumption, every standard-open-specified associated-module shift
comparison is an isomorphism. -/
#check
  (AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison.isIso_of_degreeOpen_one_eq_top :
    ∀ {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]
      (𝒜 : ℕ → Submodule ℤ A) [GradedAlgebra 𝒜]
      (ℳ : ℤ → Submodule ℤ M) [SetLike.GradedSMul 𝒜 ℳ]
      (C : AlgebraicGeometry.Proj.AssociatedModule.ShiftComparison 𝒜 ℳ),
      AlgebraicGeometry.Proj.degreeOpen 𝒜 1 = ⊤ → ∀ n : ℤ,
        IsIso (C.hom n))
