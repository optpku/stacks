/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.LinearAlgebra.Matrix.GeneralLinearGroup.ScalarKernel
public import ReasLib.Algebra.GroupCohomology.Nonabelian
public import Mathlib.Algebra.Group.Action.Units
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.Galois.IsGaloisGroup
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

@[expose] public section

universe u v

open scoped MatrixGroups

namespace GroupCohomology

variable {G : Type u} {R : Type v} [Group G] [Field R] [MulSemiringAction G R]

/-- The identity group element acts identically through entrywise maps on the general linear group. -/
theorem galoisGLAction_one_smul (d : ℕ) (A : GL (Fin d) R) :
    Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G R (1 : G)) A = A := sorry

/-- Entrywise maps on the general linear group compose according to multiplication in the acting group. -/
theorem galoisGLAction_mul_smul (d : ℕ) (σ τ : G) (A : GL (Fin d) R) :
    Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G R (σ * τ)) A =
      Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G R σ)
        (Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G R τ) A) := sorry

/-- The entrywise action induced by a group acting on a field on `GL (Fin d) R`. -/
instance galoisGLAction (d : ℕ) : MulDistribMulAction G (GL (Fin d) R) where
  smul σ A := Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G R σ) A
  one_smul := galoisGLAction_one_smul d
  mul_smul := galoisGLAction_mul_smul d
  smul_one σ := (Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G R σ)).map_one
  smul_mul σ A B :=
    (Matrix.GeneralLinearGroup.map (MulSemiringAction.toRingHom G R σ)).map_mul A B

/-- The action on units induced by a group acting on a field. -/
instance galoisUnitsAction : MulDistribMulAction G Rˣ :=
  Units.mulDistribMulActionRight

end GroupCohomology

/-- The inverse-product expression from lifts of a projective-linear one-cocycle lies in the
kernel of `GL → PGL`. -/
theorem brauerLiftProduct_mk_eq_one
    {G : Type u} {R : Type v} [Group G] [Field R] [MulSemiringAction G R]
    (d : ℕ) (c : G → PGL(d, R))
    (lift : G → GL (Fin d) R)
    (hc : ∀ σ τ, c (σ * τ) = c σ * σ • c τ)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = c σ) (σ τ : G) :
    Matrix.ProjGenLinGroup.mk
        ((lift σ)⁻¹ * lift (σ * τ) * (σ • (lift τ)⁻¹)) = 1 := sorry

/-- The scalar-valued boundary of a projective-linear Galois one-cocycle with chosen
general-linear lifts, using the inverse-product convention. -/
def brauerTwoCocycle
    (K : Type u) {Ksep : Type v} [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : 0 < d)
    (c : Gal(Ksep/K) → PGL(d, Ksep))
    (lift : Gal(Ksep/K) → GL (Fin d) Ksep)
    (hc : ∀ σ τ, c (σ * τ) = c σ * σ • c τ)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = c σ) :
    Gal(Ksep/K) × Gal(Ksep/K) → Ksepˣ :=
  fun p ↦ (Matrix.ProjGenLinGroup.scalarEquivKer d hd).symm
    ⟨(lift p.1)⁻¹ * lift (p.1 * p.2) * (p.1 • (lift p.2)⁻¹),
      brauerLiftProduct_mk_eq_one d c lift hc hlift p.1 p.2⟩

/-- The scalar matrix of the boundary equals the inverse-product expression in the chosen lifts. -/
theorem brauerTwoCocycle_spec
    (K : Type u) {Ksep : Type v} [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : 0 < d)
    (c : Gal(Ksep/K) → PGL(d, Ksep))
    (lift : Gal(Ksep/K) → GL (Fin d) Ksep)
    (hc : ∀ σ τ, c (σ * τ) = c σ * σ • c τ)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = c σ)
    (σ τ : Gal(Ksep/K)) :
    Matrix.GeneralLinearGroup.scalar (Fin d)
        (brauerTwoCocycle K d hd c lift hc hlift (σ, τ)) =
      (lift σ)⁻¹ * lift (σ * τ) * (σ • (lift τ)⁻¹) := sorry

/-- The scalar-valued boundary satisfies the multiplicative two-cocycle identity. -/
theorem brauerTwoCocycle_isMulCocycle₂
    (K : Type u) {Ksep : Type v} [Field K] [Field Ksep]
    [Algebra K Ksep] [IsSepClosure K Ksep]
    (d : ℕ) (hd : 0 < d)
    (c : Gal(Ksep/K) → PGL(d, Ksep))
    (lift : Gal(Ksep/K) → GL (Fin d) Ksep)
    (hc : ∀ σ τ, c (σ * τ) = c σ * σ • c τ)
    (hlift : ∀ σ, Matrix.ProjGenLinGroup.mk (lift σ) = c σ) :
    groupCohomology.IsMulCocycle₂ (brauerTwoCocycle K d hd c lift hc hlift) := sorry

end
