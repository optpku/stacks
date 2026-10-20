module

public import ReasLib.NumberTheory.Automorphic.CuspForms.Finiteness
public import ReasLib.NumberTheory.Automorphic.Hecke
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Algebraicity of Hecke eigenvalues

This file records algebraicity results for Hecke eigenvalues on fixed-character cusp forms.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

universe u v

namespace AlgebraicGeometry.SchemeOverField.CuspForms

variable {k : Type u} [Field k] [Fintype k]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
variable {Λ : Type v} [Field Λ] [Invertible (ringChar k : Λ)]

/-- Every eigenvalue of a Hecke endomorphism on fixed-character cusp forms is algebraic over the prime subfield. -/
theorem heckeT_eigenvalue_isAlgebraic
    (character : closedPoints X.left → (⊥ : Subfield Λ)ˣ)
    (v : closedPoints X.left) {t : Λ}
    (ht : Module.End.HasEigenvalue
      (heckeT (Units.map (algebraMap (⊥ : Subfield Λ) Λ).toMonoidHom ∘ character) v) t) :
    IsAlgebraic (⊥ : Subfield Λ) t := sorry

/-- A scalar eigenvalue of a nonzero fixed-character cusp form is algebraic over the prime subfield. -/
theorem heckeT_smul_isAlgebraic
    (character : closedPoints X.left → (⊥ : Subfield Λ)ˣ)
    (v : closedPoints X.left)
    (f : CuspForms X Λ (Units.map (algebraMap (⊥ : Subfield Λ) Λ).toMonoidHom ∘ character))
    {t : Λ} (hf : f ≠ 0)
    (ht : heckeT (Units.map (algebraMap (⊥ : Subfield Λ) Λ).toMonoidHom ∘ character) v f = t • f) :
    IsAlgebraic (⊥ : Subfield Λ) t := sorry

end AlgebraicGeometry.SchemeOverField.CuspForms
