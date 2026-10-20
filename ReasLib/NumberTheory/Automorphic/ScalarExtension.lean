module

public import Mathlib.Algebra.GroupWithZero.Invertible
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.TensorProduct.Basic
public import ReasLib.NumberTheory.Automorphic.Hecke

/-! # Coefficient extension of fixed-character cusp forms -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct

noncomputable section

universe u v

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Fintype k]
variable {Λ : Type v} [CommRing Λ] [Invertible (ringChar k : Λ)]
variable {X : SchemeOverField k}
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]

namespace CuspForms

/-- Postcomposition with a coefficient ring homomorphism preserves the four defining
conditions, with the character mapped by the same homomorphism. -/
theorem mapRingHom_mem {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    (hom : F →+* Λ) (character : closedPoints X.left → Fˣ)
    (form : CuspForms X F character) :
    (fun point ↦ hom (form.toFun point)) ∈
      cuspFormsSubmodule X Λ (Units.map hom.toMonoidHom ∘ character) := sorry

/-- Extend the coefficients of a cusp form by postcomposing its values with a ring homomorphism. -/
def mapRingHom {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    (hom : F →+* Λ) (character : closedPoints X.left → Fˣ)
    (form : CuspForms X F character) :
    CuspForms X Λ (Units.map hom.toMonoidHom ∘ character) :=
  ⟨fun point ↦ hom (form.toFun point), mapRingHom_mem hom character form⟩

/-- A coefficient map evaluates by applying the ring homomorphism to the original value. -/
theorem mapRingHom_apply {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    (hom : F →+* Λ) (character : closedPoints X.left → Fˣ)
    (form : CuspForms X F character) (point : GL (Fin 2) (adeleRing X)) :
    (mapRingHom hom character form).toFun point = hom (form.toFun point) := sorry

/-- Coefficient extension along an algebra map respects addition and the source scalar action. -/
theorem mapRingHom_linear {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    [Algebra F Λ] (character : closedPoints X.left → Fˣ) :
    (∀ first second : CuspForms X F character,
      mapRingHom (algebraMap F Λ) character (first + second) =
        mapRingHom (algebraMap F Λ) character first +
          mapRingHom (algebraMap F Λ) character second) ∧
      (∀ (scalar : F) (form : CuspForms X F character),
        mapRingHom (algebraMap F Λ) character (scalar • form) =
          scalar • mapRingHom (algebraMap F Λ) character form) := sorry

/-- Coefficient extension along an algebra map as a linear map over the source coefficient ring. -/
def mapRingHomLinear {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    [Algebra F Λ] (character : closedPoints X.left → Fˣ) :
    CuspForms X F character →ₗ[F]
      CuspForms X Λ (Units.map (algebraMap F Λ).toMonoidHom ∘ character) where
  toFun := mapRingHom (algebraMap F Λ) character
  map_add' := (mapRingHom_linear character).1
  map_smul' := (mapRingHom_linear character).2

/-- The canonical scalar-extension map from the tensor product of cusp forms to
cusp forms over the larger coefficient ring. -/
def baseChange {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    [Algebra F Λ] (character : closedPoints X.left → Fˣ) :
    Λ ⊗[F] CuspForms X F character →ₗ[Λ]
      CuspForms X Λ (Units.map (algebraMap F Λ).toMonoidHom ∘ character) :=
  LinearMap.liftBaseChange Λ (mapRingHomLinear character)

/-- On elementary tensors, scalar extension is coefficient extension followed by scaling. -/
theorem baseChange_tmul {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    [Algebra F Λ] (character : closedPoints X.left → Fˣ) (scalar : Λ)
    (form : CuspForms X F character) :
    baseChange character (scalar ⊗ₜ form) =
      scalar • mapRingHom (algebraMap F Λ) character form := sorry

/-- Scalar extension intertwines every Hecke endomorphism as an equality of composed linear maps. -/
theorem baseChange_heckeT {F : Type v} [CommRing F] [Invertible (ringChar k : F)]
    [Algebra F Λ] (character : closedPoints X.left → Fˣ) (place : closedPoints X.left) :
    heckeT (Units.map (algebraMap F Λ).toMonoidHom ∘ character) place ∘ₗ baseChange character =
      baseChange character ∘ₗ LinearMap.baseChange Λ (heckeT character place) := sorry

/-- A characteristic invertible in a coefficient field is nonzero in its prime subfield. -/
theorem ringChar_primeSubfield_ne_zero {Λ : Type v} [Field Λ]
    [Invertible (ringChar k : Λ)] :
    (ringChar k : (⊥ : Subfield Λ)) ≠ 0 := sorry

/-- A characteristic invertible in a coefficient field is invertible in its prime subfield. -/
instance instInvertible_ringChar_primeSubfield {Λ : Type v} [Field Λ]
    [Invertible (ringChar k : Λ)] : Invertible (ringChar k : (⊥ : Subfield Λ)) :=
  invertibleOfNonzero ringChar_primeSubfield_ne_zero

end CuspForms

end AlgebraicGeometry.SchemeOverField
