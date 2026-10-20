/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import ReasLib.RingTheory.CompleteIntersection.RelativeGlobal.Local
public import ReasLib.RingTheory.Extension.Cotangent.NaiveComplex
public import ReasLib.RingTheory.Extension.Presentation.Jacobian

@[expose] public section

/-!
# Coordinate generators for cotangent determinant lines

For a square polynomial presentation, this file records the ordered exterior
wedges determined by its equations and variables. A chosen relation-class
basis then identifies the coordinate determinant line with the base ring.
-/

noncomputable section

universe u v

namespace Algebra.Presentation.CotangentDeterminant

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {n : ℕ}

/-- The ordered top exterior product of a chosen basis of the conormal module. -/
def relationWedge (P : Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent) :
    ⋀[B]^n P.toExtension.Cotangent :=
  exteriorPower.ιMulti B n b

/-- The ordered top exterior product of the coordinate differentials of a presentation. -/
def differentialWedge (P : Presentation A B (Fin n) (Fin n)) :
    ⋀[B]^n P.toExtension.CotangentSpace :=
  exteriorPower.ιMulti B n P.toGenerators.cotangentSpaceBasis

/-- The generator of the coordinate determinant line determined by a relation basis. -/
def generator (P : Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent) :
    (⋀[B]^n P.toExtension.Cotangent) →ₗ[B]
      ⋀[B]^n P.toExtension.CotangentSpace :=
  LinearMap.smulRight
    (exteriorPower.alternatingMapLinearEquiv b.det)
    (differentialWedge P)

/-- The coordinate determinant generator sends the relation wedge to the differential wedge. -/
theorem generator_apply (P : Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent) :
    generator P b (relationWedge P b) = differentialWedge P := sorry

/-- Every element of the coordinate determinant line is a unique scalar multiple of its displayed generator. -/
theorem generator_uniqueScalar (P : Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent)
    (φ : (⋀[B]^n P.toExtension.Cotangent) →ₗ[B]
      ⋀[B]^n P.toExtension.CotangentSpace) :
    ∃! a : B, φ = a • generator P b := sorry

/-- The top exterior-power map induced by the presentation cotangent differential. -/
def canonicalSection (P : Presentation A B (Fin n) (Fin n)) :
    (⋀[B]^n P.toExtension.Cotangent) →ₗ[B]
      ⋀[B]^n P.toExtension.CotangentSpace :=
  exteriorPower.map n P.toExtension.cotangentComplex

/-- In relation and coordinate bases, the canonical section sends the relation wedge to the Jacobian determinant times the coordinate-differential wedge. -/
theorem canonicalSection_apply_relationWedge (P : Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent)
    (hb : ∀ i, b i = Extension.Cotangent.mk
      ⟨P.relation i, P.relation_mem_ker i⟩) :
    canonicalSection P (relationWedge P b) =
      Matrix.det (Jacobian.target P) • differentialWedge P := sorry

/-- In relation and coordinate bases, the top exterior-power cotangent differential is multiplication by the presentation Jacobian determinant. -/
theorem section_eq_smul_generator (P : Presentation A B (Fin n) (Fin n))
    (b : Module.Basis (Fin n) B P.toExtension.Cotangent)
    (hb : ∀ i, b i = Extension.Cotangent.mk
      ⟨P.relation i, P.relation_mem_ker i⟩) :
    canonicalSection P =
      Matrix.det (Jacobian.target P) • generator P b := sorry

end Algebra.Presentation.CotangentDeterminant
