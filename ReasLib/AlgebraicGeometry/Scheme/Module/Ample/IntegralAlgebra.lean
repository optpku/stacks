/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.FiniteSet

/-!
# Affine nonvanishing opens containing integral-algebra images

An ample invertible module supplies affine nonvanishing opens through which morphisms from
spectra of integral algebras over fields factor.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.IsAmple

/-- A morphism from the spectrum of an integral algebra over a field to an open subscheme
factors through an affine nonvanishing open of a positive tensor-power section contained in
that open. -/
theorem exists_affineNonvanishingOpen_factorization_of_isIntegral
    {X : Scheme.{u}} {L : X.Modules} [hL : Invertible L] [IsAmple L]
    (W : X.Opens) (k A : Type u) [Field k] [CommRing A]
    [Algebra k A] [Algebra.IsIntegral k A]
    (toW : Spec (CommRingCat.of A) ⟶ W.toScheme) :
    ∃ n : ℕ+,
      ∃ s : Γ(RingedSpace.TensorPower.sheaf L n, ⊤),
        ∃ _ : IsAffineOpen (hL.nonvanishingOpen s),
          ∃ hsub : hL.nonvanishingOpen s ≤ W,
            ∃ lift : Spec (CommRingCat.of A) ⟶ (hL.nonvanishingOpen s).toScheme,
              lift ≫ X.homOfLE hsub = toW := sorry

end AlgebraicGeometry.Scheme.Modules.IsAmple
