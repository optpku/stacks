/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import ReasLib.NumberTheory.Automorphic.CuspForm
public import ReasLib.NumberTheory.Automorphic.Eigenform
public import ReasLib.NumberTheory.Automorphic.Hecke

@[expose] public section
open AlgebraicGeometry AlgebraicGeometry.Scheme Matrix
open Finset
noncomputable section
universe u v
namespace AlgebraicGeometry.SchemeOverField
variable {k : Type u} [Field k]
variable {Λ : Type v} [CommRing Λ]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
variable [Fintype k] [Invertible (ringChar k : Λ)]

/-- A completed residue representative obtained from the canonical integral residue section. -/
def residueRep (v : closedPoints X.left) (a : X.left.residueField v.1) : completion X v :=
  (residueSectionIntegers X v a).val

/-- Canonical residue representatives lie in the local integers. -/
theorem residueRep_mem_integers (v : closedPoints X.left) (a : X.left.residueField v.1) :
    residueRep X v a ∈ completionIntegers X v := (residueSectionIntegers X v a).property

/-- A family is a system of residue representatives modulo a uniformizer. -/
def IsResidueReps (v : closedPoints X.left) (π : (completion X v)ˣ)
    (reps : X.left.residueField v.1 → completion X v) : Prop :=
  (∀ a, reps a ∈ completionIntegers X v) ∧
    ∀ a, Valued.v (reps a - residueRep X v a) ≤ Valued.v π.val

/-- The predicate for residue representatives unfolds to its defining conditions. -/
theorem isResidueReps_iff (v : closedPoints X.left) (π : (completion X v)ˣ)
    (reps : X.left.residueField v.1 → completion X v) :
    IsResidueReps X v π reps ↔
      (∀ a, reps a ∈ completionIntegers X v) ∧
        ∀ a, Valued.v (reps a - residueRep X v a) ≤ Valued.v π.val := Iff.rfl

/-- The canonical residue representatives form a residue-representative system. -/
theorem residueRep_isResidueReps (v : closedPoints X.left)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val) :
    IsResidueReps X v π (residueRep X v) := sorry

/-- The central inverse-uniformizer matrix in the adelic general linear group. -/
def heckeUMatrix (v : closedPoints X.left) (π : (completion X v)ˣ) :
    GL (Fin 2) (adeleRing X) :=
  GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π)⁻¹

/-- The central Hecke matrix is the scalar inverse of the local idèle. -/
theorem heckeUMatrix_spec (v : closedPoints X.left) (π : (completion X v)ˣ) :
    heckeUMatrix X v π = GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π)⁻¹ := rfl

omit [Fintype k] in
/-- The diagonal adelic representative for the `T` operator. -/
def heckeTDiag (v : closedPoints X.left) (π : (completion X v)ˣ) :
    GL (Fin 2) (adeleRing X) := localGL X v (heckeDiag X v π)

omit [Fintype k] in
/-- The diagonal operator is represented by the explicit local diagonal matrix. -/
theorem heckeTDiag_spec (v : closedPoints X.left) (π : (completion X v)ˣ) :
    (heckeTDiag X v π).val =
      localMatrix X v (Matrix.diagonal (fun i : Fin 2 ↦ if i = 0 then π.inv else 1)) := rfl

omit [Fintype k] in
/-- The lower-triangular adelic representative for a residue class in `T`. -/
def heckeTOff (v : closedPoints X.left) (π : (completion X v)ˣ)
    (lval : completion X v) : GL (Fin 2) (adeleRing X) :=
  localGL X v (heckeUnip X v π lval)

omit [Fintype k] in
/-- The off-diagonal operator is represented by the explicit local triangular matrix. -/
theorem heckeTOff_spec (v : closedPoints X.left) (π : (completion X v)ˣ)
    (lval : completion X v) :
    (heckeTOff X v π lval).val =
      localMatrix X v !![1, 0; -π.inv * lval, π.inv] := rfl

/-- Scalar multiplication preserves the invariance and cuspidality conditions. -/
theorem UnramifiedCuspForm.smul_mem (a : Λ) (φ : UnramifiedCuspForm X Λ) :
    IsRightInvariant X (fun x ↦ a * φ.toFun x) ∧
      IsLeftInvariant X (fun x ↦ a * φ.toFun x) ∧
        IsCuspidal X (fun x ↦ a * φ.toFun x) := sorry

/-- Scale an unramified cusp form pointwise by a coefficient. -/
def UnramifiedCuspForm.smul (a : Λ) (φ : UnramifiedCuspForm X Λ) : UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X (fun x ↦ a * φ.toFun x)
    (UnramifiedCuspForm.smul_mem X a φ).1
    (UnramifiedCuspForm.smul_mem X a φ).2.1
    (UnramifiedCuspForm.smul_mem X a φ).2.2

/-- The scaled cusp form evaluates pointwise as coefficient multiplication. -/
theorem UnramifiedCuspForm.smul_toFun (a : Λ) (φ : UnramifiedCuspForm X Λ) :
    (UnramifiedCuspForm.smul X a φ).toFun = fun x ↦ a * φ.toFun x := rfl

/-- The central `U` translation preserves cusp-form conditions. -/
theorem heckeU_mem (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    IsRightInvariant X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x)) ∧
      IsLeftInvariant X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x)) ∧
        IsCuspidal X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x)) := sorry

/-- The unramified `U` operator. -/
def heckeU (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X (fun x ↦ φ.toFun (heckeUMatrix X v (uniformizer X v) * x))
    (heckeU_mem X v φ).1 (heckeU_mem X v φ).2.1 (heckeU_mem X v φ).2.2

/-- The `U` operator evaluates by translation by any uniformizer matrix. -/
theorem heckeU_spec (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (x : GL (Fin 2) (adeleRing X)) :
    (heckeU X v φ).toFun x = φ.toFun (heckeUMatrix X v π * x) := sorry

/-- The `U` translation is independent of the chosen uniformizer. -/
theorem heckeU_independent (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π π' : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (hπ' : IsUniformizer X v π'.val) (x : GL (Fin 2) (adeleRing X)) :
    φ.toFun (heckeUMatrix X v π * x) = φ.toFun (heckeUMatrix X v π' * x) := sorry

/-- The finite-sum `T` translation preserves cusp-form conditions. -/
theorem heckeT_mem (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    IsRightInvariant X (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x)) ∧
      IsLeftInvariant X (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x)) ∧
        IsCuspidal X (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x)) := sorry

/-- The finite-sum unramified `T` operator. -/
def heckeT (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X
    (fun x ↦ φ.toFun (heckeTDiag X v (uniformizer X v) * x) +
      ∑ a : X.left.residueField v.1,
        φ.toFun (heckeTOff X v (uniformizer X v) (residueRep X v a) * x))
    (heckeT_mem X v φ).1 (heckeT_mem X v φ).2.1 (heckeT_mem X v φ).2.2

/-- The `T` operator evaluates by its diagonal and residue-indexed translations. -/
theorem heckeT_spec (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (reps : X.left.residueField v.1 → completion X v)
    (hreps : IsResidueReps X v π reps) (x : GL (Fin 2) (adeleRing X)) :
    (heckeT X v φ).toFun x = φ.toFun (heckeTDiag X v π * x) +
      ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v π (reps a) * x) := sorry

/-- The finite-sum `T` operator is independent of uniformizers and representatives. -/
theorem heckeT_independent (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π π' : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (hπ' : IsUniformizer X v π'.val)
    (reps reps' : X.left.residueField v.1 → completion X v)
    (hreps : IsResidueReps X v π reps) (hreps' : IsResidueReps X v π' reps')
    (x : GL (Fin 2) (adeleRing X)) :
    φ.toFun (heckeTDiag X v π * x) + ∑ a, φ.toFun (heckeTOff X v π (reps a) * x) =
      φ.toFun (heckeTDiag X v π' * x) + ∑ a, φ.toFun (heckeTOff X v π' (reps' a) * x) := sorry

/-- An unramified cusp form is an eigenform for the Hecke system `f`. -/
def IsEigenform (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ) : Prop :=
  (∃ x, IsUnit (φ.toFun x)) ∧
    (∀ v, heckeT X v φ = UnramifiedCuspForm.smul X (f.t v) φ) ∧
    (∀ v, heckeU X v φ = UnramifiedCuspForm.smul X (f.u v).val φ)

/-- The eigenform predicate is equivalent to its nonvanishing and two eigen-equations. -/
theorem isEigenform_iff (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ) :
    IsEigenform X φ f ↔
      (∃ x, IsUnit (φ.toFun x)) ∧
        (∀ v, heckeT X v φ = UnramifiedCuspForm.smul X (f.t v) φ) ∧
        (∀ v, heckeU X v φ = UnramifiedCuspForm.smul X (f.u v).val φ) := Iff.rfl

/-- The nonvanishing condition in the definition of an eigenform. -/
theorem isEigenform_isUnit (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) : ∃ x, IsUnit (φ.toFun x) := hφ.1

/-- The `T` eigen-equation of an unramified cusp eigenform. -/
theorem isEigenform_heckeT (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) (v : closedPoints X.left) :
    heckeT X v φ = UnramifiedCuspForm.smul X (f.t v) φ := hφ.2.1 v

/-- The `U` eigen-equation of an unramified cusp eigenform. -/
theorem isEigenform_heckeU (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) (v : closedPoints X.left) :
    heckeU X v φ = UnramifiedCuspForm.smul X (f.u v).val φ := hφ.2.2 v

end AlgebraicGeometry.SchemeOverField
