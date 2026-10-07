module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.AffineBase
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.FlatBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.Characterization

/-!
# Serre Vanishing for Higher Direct Images

This module records eventual vanishing of positive higher direct images of coherent modules
twisted by relatively ample invertible modules along proper morphisms over Noetherian schemes.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.HigherDirectImage

variable {X S : Scheme.{u}}

/-- Along a proper morphism to a Noetherian scheme, the positive higher direct images of a
coherent quasicoherent module twisted by sufficiently large powers of a relatively ample
invertible module vanish, with one bound uniform in every positive degree. -/
theorem properRelativelyAmpleCoherentTwist_eventually_isZero
    (f : X ⟶ S) [IsNoetherian S] [IsProper f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsCoherent]
    (L : X.Modules) [L.Invertible] [RelativelyAmple f L] :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ p : ℕ, 0 < p →
      IsZero (AlgebraicGeometry.RingedSpace.Hom.higherDirectImageModule f.toShHom
        (F ⊗ L ^⊗ (n : ℤ)) p) := sorry

end AlgebraicGeometry.Scheme.HigherDirectImage
