module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.NumberTheory.Automorphic.ScalarExtension

/-! # Finiteness and prime-field descent of fixed-character cusp forms -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

noncomputable section

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {p : ℕ} [Fact p.Prime] [CharP k p]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
variable [ConnectedSpace X.left]

namespace CuspForms

/-- Fixed-character unramified cusp forms over a Noetherian coefficient ring form
a finitely generated module. -/
instance moduleFinite {Λ : Type v} [CommRing Λ] [Invertible (ringChar k : Λ)]
    [IsNoetherianRing Λ] (character : closedPoints X.left → Λˣ) :
    Module.Finite Λ (CuspForms X Λ character) := sorry

/-- Extending a prime-subfield-valued central character to a coefficient field induces
a bijective canonical scalar-extension map on cusp forms. -/
theorem baseChange_bijective {Λ : Type v} [Field Λ] [Invertible (ringChar k : Λ)]
    (character : closedPoints X.left → (⊥ : Subfield Λ)ˣ) :
    Function.Bijective
      (baseChange character :
        Λ ⊗[(⊥ : Subfield Λ)] CuspForms X (⊥ : Subfield Λ) character →ₗ[Λ]
          CuspForms X Λ
            (Units.map (algebraMap (⊥ : Subfield Λ) Λ).toMonoidHom ∘ character)) := sorry

end CuspForms

end AlgebraicGeometry.SchemeOverField
