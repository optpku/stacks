module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import stacks_project.Chap64.Proposition_64_31_5_CuspForms
public import stacks_project.Chap64.Theorem_64_31_2_Eigenform
public import stacks_project.Chap64.Theorem_64_31_2_Frobenius

/-!
# Hecke operators on unramified GL₂ cusp forms

Source operators `U_v` and `T_v` on `UnramifiedCuspForm`, together with the
eigenform predicate relating a cusp form to its Hecke eigenvalue system.
Uniformizer and residue-representative choices are packaged behind spec and
independence lemmas.
-/

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

/-- The value in `K_v` of a chosen uniformizer at the closed point `v`. -/
def chosenUniformizerVal (v : closedPoints X.left) : completion X v :=
  algebraMap X.left.functionField (completion X v)
    (Classical.choose
      ((place X v).valuation_exists_uniformizer X.left.functionField))

/-- A chosen uniformizer `π_v ∈ K_vˣ` at the closed point `v`. -/
def chosenUniformizer (v : closedPoints X.left) : (completion X v)ˣ where
  val := chosenUniformizerVal X v
  inv := (chosenUniformizerVal X v)⁻¹
  val_inv := sorry
  inv_val := sorry

/-- The chosen local parameter is a uniformizer of `K_v`. -/
theorem chosenUniformizer_spec (v : closedPoints X.left) :
    IsUniformizer X v (chosenUniformizer X v).val := sorry

/-- A chosen lift of a residue class at `v` into `O_v ⊂ K_v`. -/
def residueRep (v : closedPoints X.left) (a : X.left.residueField v.1) :
    completion X v :=
  algebraMap X.left.functionField (completion X v)
    (algebraMap (X.left.presheaf.stalk v.1) X.left.functionField (Quotient.out a))

/-- Each chosen residue lift lies in the local integers `O_v`. -/
theorem residueRep_mem_integers (v : closedPoints X.left)
    (a : X.left.residueField v.1) :
    residueRep X v a ∈ completionIntegers X v := sorry

/-- A family `λ` is a complete set of representatives of `O_v / π_v ≃ κ(v)`. -/
def IsResidueReps (v : closedPoints X.left) (π : (completion X v)ˣ)
    (reps : X.left.residueField v.1 → completion X v) : Prop :=
  (∀ a, reps a ∈ completionIntegers X v) ∧
    ∀ a, Valued.v (reps a - residueRep X v a) ≤ Valued.v π.val

/-- Unfolding of the complete-representatives condition. -/
theorem isResidueReps_iff (v : closedPoints X.left) (π : (completion X v)ˣ)
    (reps : X.left.residueField v.1 → completion X v) :
    IsResidueReps X v π reps ↔
      (∀ a, reps a ∈ completionIntegers X v) ∧
        ∀ a, Valued.v (reps a - residueRep X v a) ≤ Valued.v π.val := sorry

/-- The chosen residue lifts are a complete set of representatives for any
uniformizer. -/
theorem residueRep_isResidueReps (v : closedPoints X.left)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val) :
    IsResidueReps X v π (residueRep X v) := sorry

/-- The diagonal matrix `diag(π_v⁻¹, π_v⁻¹)` embedded in `GL (Fin 2) A`. -/
def heckeUMatrix (v : closedPoints X.left) (π : (completion X v)ˣ) :
    GL (Fin 2) (adeleRing X) :=
  GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π)⁻¹

/-- `heckeUMatrix` is the central scalar matrix of the inverse uniformizer
idele. -/
theorem heckeUMatrix_spec (v : closedPoints X.left) (π : (completion X v)ˣ) :
    heckeUMatrix X v π =
      GeneralLinearGroup.scalar (Fin 2) (localAdeleUnit X v π)⁻¹ := sorry

/-- The diagonal matrix `diag(π_v⁻¹, 1)` embedded in `GL (Fin 2) A`. -/
def heckeTDiag (v : closedPoints X.left) (π : (completion X v)ˣ) :
    GL (Fin 2) (adeleRing X) where
  val := Matrix.diagonal ![localAdele X v π.val⁻¹, 1]
  inv := Matrix.diagonal ![localAdele X v π.val, 1]
  val_inv := sorry
  inv_val := sorry

/-- Unfolding of `heckeTDiag` as the diagonal matrix with `π_v⁻¹` and `1`. -/
theorem heckeTDiag_spec (v : closedPoints X.left) (π : (completion X v)ˣ) :
    (heckeTDiag X v π).val = Matrix.diagonal ![localAdele X v π.val⁻¹, 1] :=
  sorry

/-- The matrix `!![1, 0; -π_v⁻¹ λ, π_v⁻¹]` embedded in `GL (Fin 2) A`. -/
def heckeTOff (v : closedPoints X.left) (π : (completion X v)ˣ)
    (lval : completion X v) : GL (Fin 2) (adeleRing X) where
  val := !![1, 0; localAdeleZero X v (-π.val⁻¹ * lval), localAdele X v π.val⁻¹]
  inv := !![1, 0; localAdeleZero X v lval, localAdele X v π.val]
  val_inv := sorry
  inv_val := sorry

/-- Unfolding of `heckeTOff` as the displayed lower-triangular local matrix. -/
theorem heckeTOff_spec (v : closedPoints X.left) (π : (completion X v)ˣ)
    (lval : completion X v) :
    (heckeTOff X v π lval).val =
      !![1, 0; localAdeleZero X v (-π.val⁻¹ * lval), localAdele X v π.val⁻¹] :=
  sorry

variable [Fintype k] [Invertible (ringChar k : Λ)]

/-- Pointwise scalar multiplication of unramified cusp forms. -/
instance instSMul_unramifiedCuspForm : SMul Λ (UnramifiedCuspForm X Λ) where
  smul a φ := UnramifiedCuspForm.of X (fun x ↦ a * φ.toFun x) sorry sorry sorry

/-- The Hecke operator `U_v` on unramified cusp forms. -/
def heckeU (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X
    (fun x ↦ φ.toFun (heckeUMatrix X v (chosenUniformizer X v) * x))
    sorry sorry sorry

/-- `U_v(φ)(x) = φ(diag(π_v⁻¹, π_v⁻¹) x)` for every uniformizer `π_v`. -/
theorem heckeU_spec (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (x : GL (Fin 2) (adeleRing X)) :
    (heckeU X v φ).toFun x = φ.toFun (heckeUMatrix X v π * x) := sorry

/-- The operator `U_v` is independent of the choice of uniformizer. -/
theorem heckeU_independent (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π π' : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (hπ' : IsUniformizer X v π'.val) (x : GL (Fin 2) (adeleRing X)) :
    φ.toFun (heckeUMatrix X v π * x) = φ.toFun (heckeUMatrix X v π' * x) :=
  sorry

/-- The Hecke operator `T_v` on unramified cusp forms. -/
def heckeT (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ) :
    UnramifiedCuspForm X Λ :=
  UnramifiedCuspForm.of X
    (fun x ↦
      φ.toFun (heckeTDiag X v (chosenUniformizer X v) * x) +
        ∑ a : X.left.residueField v.1,
          φ.toFun
            (heckeTOff X v (chosenUniformizer X v) (residueRep X v a) * x))
    sorry sorry sorry

/-- `T_v(φ)(x) = φ(diag(π_v⁻¹, 1) x) + ∑_λ φ(!![1, 0; -π_v⁻¹ λ, π_v⁻¹] x)`
for every uniformizer and complete set of residue representatives. -/
theorem heckeT_spec (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (reps : X.left.residueField v.1 → completion X v)
    (hreps : IsResidueReps X v π reps) (x : GL (Fin 2) (adeleRing X)) :
    (heckeT X v φ).toFun x =
      φ.toFun (heckeTDiag X v π * x) +
        ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v π (reps a) * x) :=
  sorry

/-- The operator `T_v` is independent of the uniformizer and of the residue
representatives. -/
theorem heckeT_independent (v : closedPoints X.left) (φ : UnramifiedCuspForm X Λ)
    (π π' : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (hπ' : IsUniformizer X v π'.val)
    (reps reps' : X.left.residueField v.1 → completion X v)
    (hreps : IsResidueReps X v π reps) (hreps' : IsResidueReps X v π' reps')
    (x : GL (Fin 2) (adeleRing X)) :
    φ.toFun (heckeTDiag X v π * x) +
        ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v π (reps a) * x) =
      φ.toFun (heckeTDiag X v π' * x) +
        ∑ a : X.left.residueField v.1, φ.toFun (heckeTOff X v π' (reps' a) * x) :=
  sorry

/-- An unramified cusp form is an eigenform for the Hecke system `f` when some
value is a unit and `T_v φ = f.t v • φ`, `U_v φ = (f.u v).val • φ`. -/
def IsEigenform (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ) : Prop :=
  (∃ x, IsUnit (φ.toFun x)) ∧
    (∀ v, heckeT X v φ = f.t v • φ) ∧
    (∀ v, heckeU X v φ = (f.u v).val • φ)

/-- Unfolding of the eigenform predicate into a unit value and the Hecke
eigen-equations. -/
theorem isEigenform_iff (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ) :
    IsEigenform X φ f ↔
      (∃ x, IsUnit (φ.toFun x)) ∧
        (∀ v, heckeT X v φ = f.t v • φ) ∧
        (∀ v, heckeU X v φ = (f.u v).val • φ) := sorry

/-- An eigenform takes a unit value. -/
theorem isEigenform_isUnit (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) : ∃ x, IsUnit (φ.toFun x) := sorry

/-- An eigenform is a `T_v`-eigenvector with eigenvalue `f.t v`. -/
theorem isEigenform_heckeT (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) (v : closedPoints X.left) :
    heckeT X v φ = f.t v • φ := sorry

/-- An eigenform is a `U_v`-eigenvector with eigenvalue `(f.u v).val`. -/
theorem isEigenform_heckeU (φ : UnramifiedCuspForm X Λ) (f : Eigenform X Λ)
    (hφ : IsEigenform X φ f) (v : closedPoints X.left) :
    heckeU X v φ = (f.u v).val • φ := sorry

end AlgebraicGeometry.SchemeOverField
