/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.SectionCompletion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 29.34.20: a morphism smooth at a point on a section admits compatible affine
neighborhoods whose conormal module is free and whose completed coordinate ring is a
finite-variable formal power series algebra. -/
@[stacks 05D9] #check
  (AlgebraicGeometry.Scheme.Hom.exists_affineOpen_section_conormal_free_and_completion :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (σ : S ⟶ X) (_ : σ ≫ f = 𝟙 S)
      (s : S) (_ : f.SmoothAt (σ s)),
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
                      MvPowerSeries (Fin d) A))
