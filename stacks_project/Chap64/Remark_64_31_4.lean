/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.Complex
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Instances.Matrix
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import stacks_project.Chap64.Remark_64_31_4_Eigenform
public import stacks_project.Chap64.Theorem_64_31_10_GLRep
public import stacks_project.Chap64.Theorem_64_31_2_Frobenius
public import stacks_project.Chap64.Theorem_64_31_2_Hecke
public import stacks_project.Chap64.Theorem_64_31_3_Attachment

/-!
# Global Langlands correspondence for GLₙ over function fields

Remark 64.31.4 records that the two Drinfeld existence theorems for unramified
`GL (Fin 2)` extend to `GL (Fin n)` with ramification: cuspidal Hecke eigenforms
on a nonempty open `U ⊆ X` correspond to continuous absolutely irreducible
`ℓ`-adic representations of `π₁(U)` matching geometric Frobenius characteristic
polynomials. Questions remaining about `π₁` of curves over finite fields are
left to later items.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.SchemeOverField
open CategoryTheory Matrix Matrix.GeneralLinearGroup TopologicalSpace

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k] [Finite k]
variable {p ℓ : ℕ} [Fact p.Prime] [CharP k p] [Fact ℓ.Prime]
variable (X : SchemeOverField k)
variable [Curve X] [Smooth X.hom] [Projective X.hom] [GeometricallyIrreducible X.hom]
variable [ConnectedSpace X.left]

/-- Remark 64.31.4 (1). An eigenform for `GL (Fin n)` on a nonempty open
`U ⊆ X`, with values in `PadicAlgCl ℓ` and `ℓ ≠ p`, yields a continuous
absolutely irreducible representation `ρ : π₁(U, xbar) →ₜ* GL (Fin n) E` on a
finite extension `E` of `ℚ_[ℓ]` contained in `PadicAlgCl ℓ`, matching Frobenius
characteristic polynomials at every closed point of `U`. -/
@[stacks 03VV]
theorem exists_galoisRepresentation_of_eigenformGL {n : ℕ} (hℓ : ℓ ≠ p)
    (U : X.left.Opens) [Nonempty U] [ConnectedSpace (openRestrict X U).left]
    (xbar : GeometricPoint (openRestrict X U).left)
    (φ : CuspFormGL X n U (PadicAlgCl ℓ))
    (f : EigenformGL X n U (PadicAlgCl ℓ))
    (hφ : IsEigenformGL X n U φ f)
    (h_lambda : EigenformGL.lambda_last_is_integral_unit f) :
    ∃ (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
      (hE : FiniteDimensional ℚ_[ℓ] E)
      (ρ : etaleFundamentalGroup (openRestrict X U).left xbar →ₜ* GL (Fin n) E),
      IsAbsolutelyIrreducible ρ.toMonoidHom ∧ f.IsAttachedTo ρ := sorry

/-- Remark 64.31.4 (2). A continuous absolutely irreducible representation
`ρ : π₁(U, xbar) →ₜ* GL (Fin n) E` on a finite extension `E` of `ℚ_[ℓ]`
contained in `PadicAlgCl ℓ`, with `ℓ ≠ p`, yields an eigenform for
`GL (Fin n)` on the nonempty open `U ⊆ X` whose Frobenius characteristic
polynomials match those of `ρ` at every closed point of `U`. -/
@[stacks 03VV]
theorem exists_eigenformGL_of_galoisRepresentation {n : ℕ} (hℓ : ℓ ≠ p)
    (U : X.left.Opens) [Nonempty U] [ConnectedSpace (openRestrict X U).left]
    (xbar : GeometricPoint (openRestrict X U).left)
    (E : IntermediateField ℚ_[ℓ] (PadicAlgCl ℓ))
    [FiniteDimensional ℚ_[ℓ] E]
    (ρ : etaleFundamentalGroup (openRestrict X U).left xbar →ₜ* GL (Fin n) E)
    (hρ : IsAbsolutelyIrreducible ρ.toMonoidHom) :
    ∃ (φ : CuspFormGL X n U (PadicAlgCl ℓ))
      (f : EigenformGL X n U (PadicAlgCl ℓ)),
      IsEigenformGL X n U φ f ∧
        EigenformGL.lambda_last_is_integral_unit f ∧ f.IsAttachedTo ρ := sorry

/-- An unramified `GL (Fin 2)` cusp form is a `CuspFormGL` on the full open
`⊤`, of trivial level. -/
def UnramifiedCuspForm.toCuspFormGL {Λ : Type u} [CommRing Λ] [Fintype k]
    [Invertible (ringChar k : Λ)] (φ : UnramifiedCuspForm X Λ) :
    CuspFormGL X 2 ⊤ Λ :=
  CuspFormGL.of φ.toFun sorry sorry (fun _ ↦ 0) sorry sorry

/-- For `GL (Fin 2)`, vanishing of constant terms along proper standard
parabolic radicals agrees with `IsCuspidal`. -/
theorem isCuspidalGL_two_iff {Λ : Type u} [CommRing Λ]
    [Invertible (ringChar k : Λ)]
    (f : GL (Fin 2) (adeleRing X) → Λ) :
    IsCuspidalGL X 2 f ↔ IsCuspidal X f := sorry

/-- The line at infinity gives the left integral coset of `heckeTDiag`.
The change of representative is integral, so left-invariant forms have the
same translate. -/
theorem heckeCosetRep_infinity (v : closedPoints X.left)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val) :
    ∃ a : GL (Fin 2) (completionIntegers X v),
      localIntegerGL X 2 v a * heckeCosetRep X 2 v 1 (heckeLineInfinity X v) π =
        heckeTDiag X v π := sorry

/-- The affine line `(-a, 1)` gives the left integral coset of `heckeTOff a`.
Together with infinity these are exactly the `q_v + 1` rank-two left cosets. -/
theorem heckeCosetRep_affine (v : closedPoints X.left)
    (π : (completion X v)ˣ) (hπ : IsUniformizer X v π.val)
    (a : X.left.residueField v.1) :
    ∃ b : GL (Fin 2) (completionIntegers X v),
      localIntegerGL X 2 v b * heckeCosetRep X 2 v 1 (heckeLineAffine X v a) π =
        heckeTOff X v π (residueRep X v a) := sorry

/-- For `n = 2` and `U = ⊤`, the spherical operator `T_{v,1}` agrees with
`heckeT`. -/
theorem heckeTGL_heckeT {Λ : Type u} [CommRing Λ] [Fintype k]
    [Invertible (ringChar k : Λ)] (φ : UnramifiedCuspForm X Λ)
    (v : closedPoints (openRestrict X ⊤).left) :
    (heckeTGL X 2 ⊤ v 1 φ.toCuspFormGL).toFun =
      (heckeT X (closedPointEmbed X ⊤ v) φ).toFun := sorry

/-- For `n = 2` and `U = ⊤`, the spherical operator `T_{v,2}` agrees with
`heckeU`. -/
theorem heckeTGL_heckeU {Λ : Type u} [CommRing Λ] [Fintype k]
    [Invertible (ringChar k : Λ)] (φ : UnramifiedCuspForm X Λ)
    (v : closedPoints (openRestrict X ⊤).left) :
    (heckeTGL X 2 ⊤ v 2 φ.toCuspFormGL).toFun =
      (heckeU X (closedPointEmbed X ⊤ v) φ).toFun := sorry

/-- The `n = 2` Satake polynomial of the `heckeT`/`heckeU` eigenvalues
`(t_v, u_v)` is `X^2 - t_v X + (residueCard v) * u_v`. Under
`Eigenform.IsAttachedTo` this equals `Matrix.charpoly (ρ F_v)`. -/
theorem isAttachedTo_satakeCharpoly
    (xbar : GeometricPoint X.left)
    {E : Type u} [Field E] [Algebra E (PadicAlgCl ℓ)] [TopologicalSpace E]
    (f : Eigenform X (PadicAlgCl ℓ))
    (ρ : etaleFundamentalGroup X.left xbar →ₜ* GL (Fin 2) E)
    (hf : f.IsAttachedTo ρ) (v : closedPoints X.left)
    (ι : standardFiniteEtaleFiber (geometricPointOverClosedPoint X v) ≅
      standardFiniteEtaleFiber xbar) :
    Polynomial.map (algebraMap E (PadicAlgCl ℓ))
        (Matrix.charpoly (ρ (etaleGeometricFrobenius X xbar v ι)).val) =
      satakeCharpoly 2 (residueCard X v)
        (Fin.cases 1 fun j : Fin 2 ↦ if j.val = 0 then f.t v else (f.u v).val) :=
  sorry

/-- For an unramified `GL (Fin 2)` eigenform, the Satake polynomial of the
`heckeT` and `heckeU` eigenvalues is `X^2 - t_v X + (residueCard v) * u_v`. -/
theorem satakeCharpoly_heckeTU
    [Fintype k] [Invertible (ringChar k : PadicAlgCl ℓ)]
    (φ : UnramifiedCuspForm X (PadicAlgCl ℓ))
    (f : Eigenform X (PadicAlgCl ℓ)) (hφ : IsEigenform X φ f)
    (v : closedPoints X.left) :
    satakeCharpoly 2 (residueCard X v)
        (Fin.cases 1 fun j : Fin 2 ↦ if j.val = 0 then f.t v else (f.u v).val) =
      Polynomial.X ^ 2 - Polynomial.C (f.t v) * Polynomial.X +
        Polynomial.C ((residueCard X v : PadicAlgCl ℓ) * (f.u v).val) := sorry

end AlgebraicGeometry.SchemeOverField
