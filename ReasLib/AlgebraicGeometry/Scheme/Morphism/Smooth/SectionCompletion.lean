module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.AtPoint
public import ReasLib.RingTheory.Smooth.Retraction.Completion

/-!
# Formal coordinates along a smooth section

This module gives compatible affine neighborhoods of a point on a section
where the conormal module is free and the completed coordinate ring is a
finite-variable formal power series algebra.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X)

/-- At a point where a scheme morphism is smooth along a section, there are
compatible affine neighborhoods on which the section has free conormal module
and the completed coordinate ring is a finite-variable formal power series
algebra. -/
theorem exists_affineOpen_section_conormal_free_and_completion
    (hσ : σ ≫ f = 𝟙 S) (s : S) (hsmooth : f.SmoothAt (σ s)) :
    ∃ U : S.affineOpens, s ∈ (U : S.Opens) ∧
      ∃ V : X.affineOpens, σ s ∈ (V : X.Opens) ∧
        ∃ e : (V : X.Opens) ≤ f ⁻¹ᵁ (U : S.Opens),
          ∃ eσ : (U : S.Opens) ≤ σ ⁻¹ᵁ (V : X.Opens),
            let A := Γ(S, U)
            let B := Γ(X, V)
            let φ : A →+* B := (f.appLE (U : S.Opens) (V : X.Opens) e).hom
            let ρ : B →+* A := (σ.appLE (V : X.Opens) (U : S.Opens) eσ).hom
            let _ : Algebra A B := φ.toAlgebra
            Module.Free A (RingHom.ker ρ).Cotangent ∧
              ∃ d : ℕ,
                Nonempty
                  ((AdicCompletion (RingHom.ker ρ) B) ≃ₐ[A]
                    MvPowerSeries (Fin d) A) := sorry

end AlgebraicGeometry.Scheme.Hom
