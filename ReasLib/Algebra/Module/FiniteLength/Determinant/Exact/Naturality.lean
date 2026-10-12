/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.FiniteLength.Determinant.Exact
public import ReasLib.Algebra.Module.FiniteLength.Determinant.Functoriality

/-!
# Naturality of exact-sequence determinant equivalences

The determinant-line equivalence of a short exact sequence is compatible with isomorphisms
of short exact sequences.
-/

@[expose] public section

noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u v

namespace Module.FiniteLengthDeterminant

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The short-exact determinant equivalence is natural under an isomorphism of short exact
sequences. -/
theorem exactEquiv_naturality {S T : ShortComplex (ModuleCat.{v} R)}
    (hS₁ : IsFiniteLength R S.X₁) (hS₂ : IsFiniteLength R S.X₂)
    (hS₃ : IsFiniteLength R S.X₃) (hT₁ : IsFiniteLength R T.X₁)
    (hT₂ : IsFiniteLength R T.X₂) (hT₃ : IsFiniteLength R T.X₃)
    (hS : S.ShortExact) (e : S ≅ T) :
    (exactEquiv T hT₁ hT₂ hT₃ (ShortComplex.shortExact_of_iso e hS)).toLinearMap.comp
        (TensorProduct.congr
          (mapEquiv hS₁ hT₁ (ShortComplex.π₁.mapIso e).toLinearEquiv)
          (mapEquiv hS₃ hT₃ (ShortComplex.π₃.mapIso e).toLinearEquiv)).toLinearMap =
      (mapEquiv hS₂ hT₂ (ShortComplex.π₂.mapIso e).toLinearEquiv).toLinearMap.comp
        (exactEquiv S hS₁ hS₂ hS₃ hS).toLinearMap := sorry

end Module.FiniteLengthDeterminant
