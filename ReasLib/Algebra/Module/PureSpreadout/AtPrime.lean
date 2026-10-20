module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import ReasLib.Algebra.Module.PureSpreadout
public import ReasLib.LinearAlgebra.TensorProduct.RightModule
public import ReasLib.LinearAlgebra.UniversallyInjective.Localization.Relative

@[expose] public section

universe u v w

open scoped TensorProduct TensorProduct.Right

namespace Module.PureSpreadout

/-- After localizing the base ring at a prime, a finitely presented localized
module admits a pure spreadout modulo a finitely generated ideal over the local base. -/
theorem exists_atPrime
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid B) {N : Type w} [AddCommGroup N]
    [Module (Localization S) N] [Module B N] [Module A N]
    [IsScalarTower B (Localization S) N] [IsScalarTower A B N]
    (hAB : (algebraMap A B).FinitePresentation)
    [Module.FinitePresentation (Localization S) N]
    (p : PrimeSpectrum A) :
    ∃ I : Ideal (Localization.AtPrime p.asIdeal),
      I.FG ∧
        I ≤ Ideal.map (algebraMap A (Localization.AtPrime p.asIdeal)) p.asIdeal ∧
        let R := Localization.AtPrime p.asIdeal ⧸ I
        let B_R := R ⊗[A] B
        let N_R := R ⊗[A] N
        let S_R := S.map ((Algebra.TensorProduct.includeRight : B →ₐ[A] B_R).toMonoidHom)
        ∃ (s : S) (N' : Type (max u v w))
            (_ : AddCommGroup N') (_ : Module R N') (_ : Module B_R N')
            (_ : Module
              (Localization.Away
                ((Algebra.TensorProduct.includeRight : B →ₐ[A] B_R) s)) N')
            (_ : IsScalarTower R B_R N')
            (_ : IsScalarTower B_R
              (Localization.Away
                ((Algebra.TensorProduct.includeRight : B →ₐ[A] B_R) s)) N')
            (_ : Module.FinitePresentation
              (Localization.Away
                ((Algebra.TensorProduct.includeRight : B →ₐ[A] B_R) s)) N')
            (_ : Module.Projective R N'),
          ∃ ι : @LinearMap B_R B_R _ _ (RingHom.id B_R) N' N_R _ _
              (inferInstanceAs (Module B_R N'))
              (TensorProduct.Right.algebraModule : Module B_R N_R),
            @LinearMap.UniversallyInjective.overBase
                R _ B_R _ _ N' _ (inferInstanceAs (Module B_R N'))
                N_R _ (TensorProduct.Right.algebraModule : Module B_R N_R) ι ∧
              @IsLocalizedModule
                B_R _ N' N_R _ _ (inferInstanceAs (Module B_R N'))
                (TensorProduct.Right.algebraModule : Module B_R N_R) S_R ι := sorry

end Module.PureSpreadout
