module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.InternalHom.Adjunction

/-!
# Evaluation morphisms for differential graded internal Hom

The two tensor--internal-Hom adjunctions produce evaluation pairings and canonical maps into
double internal Homs.  The right-source construction records its Koszul sign already on the
homogeneous pairing, so downstream users do not need to reconstruct the sign convention.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace DifferentialGradedModule.InternalHom

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

namespace OfLeft

/-- The evaluation pairing `Hom•(M, N) ⊗_A M ⟶ N`, obtained by uncurrying the identity
of the left-source internal Hom. -/
def evaluationPairing (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    TensorProduct.complex (obj M N) M ⟶ N :=
  homEquiv (obj M N) M N (𝟙 (obj M N))

/-- The left-source evaluation pairing acts on a homogeneous pure tensor by ordinary
evaluation, with no additional Koszul sign. -/
theorem evaluationPairing_tmul (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (p q : ℤ)
    (f : (obj M N).X p) (x : M.X q) :
    (evaluationPairing M N).f (p + q) (TensorProduct.tmul (obj M N) M f x) =
      (asCochain M N f).v q (p + q) (add_comm q p) x := sorry

/-- Remark 22.13.5 (0FQ7): evaluation followed by the opposite tensor--internal-Hom
adjunction gives the canonical left-DG-module map
`M ⟶ Hom•(Hom•(M, N), N)`. -/
@[stacks 0FQ7 "left evaluation into a double differential graded internal Hom"]
def evaluation (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    M ⟶ OfRight.obj (obj M N) N :=
  (OfRight.homEquiv (obj M N) M N).symm (evaluationPairing M N)

/-- Transposing the left evaluation morphism recovers its evaluation pairing. -/
theorem evaluation_transpose (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    OfRight.homEquiv (obj M N) M N (evaluation M N) = evaluationPairing M N := sorry

/-- On homogeneous elements, the left evaluation morphism includes the Koszul sign introduced
by the right-source tensor-order comparison. -/
theorem evaluation_apply (M : LeftDifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (p q : ℤ)
    (f : (obj M N).X p) (x : M.X q) :
    (OfRight.asCochain (obj M N) N ((evaluation M N).hom q x)).v
        p (p + q) rfl f =
      ((p * q).negOnePow : R) •
        (asCochain M N f).v q (p + q) (add_comm q p) x := sorry

end OfLeft

namespace OfRight

/-- The Koszul-signed evaluation pairing `M ⊗_A Hom•(M, N) ⟶ N`, obtained by
uncurrying the identity of the right-source internal Hom. -/
def evaluationPairing (M : DifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    TensorProduct.complex M (obj M N) ⟶ N :=
  homEquiv M (obj M N) N (𝟙 (obj M N))

/-- On a homogeneous pure tensor, right-source evaluation is multiplication by the Koszul sign
`(-1) ^ (p * q)` followed by ordinary cochain evaluation. -/
theorem evaluationPairing_tmul (M : DifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (p q : ℤ)
    (m : M.X p) (f : (obj M N).X q) :
    (evaluationPairing M N).f (p + q) (TensorProduct.tmul M (obj M N) m f) =
      ((p * q).negOnePow : R) • (asCochain M N f).v p (p + q) rfl m := sorry

/-- Remark 22.13.6 (0FQ8): the signed evaluation pairing transposes to the canonical
right-DG-module map `M ⟶ Hom•(Hom•(M, N), N)`. -/
@[stacks 0FQ8 "right evaluation into a double differential graded internal Hom"]
def evaluation (M : DifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    M ⟶ OfLeft.obj (obj M N) N :=
  (OfLeft.homEquiv M (obj M N) N).symm (evaluationPairing M N)

/-- Transposing the right evaluation morphism recovers its Koszul-signed pairing. -/
theorem evaluation_transpose (M : DifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) :
    OfLeft.homEquiv M (obj M N) N (evaluation M N) = evaluationPairing M N := sorry

/-- On homogeneous elements, the right evaluation morphism sends `m` to signed evaluation by
`(-1) ^ (p * q)`. -/
theorem evaluation_apply (M : DifferentialGradedModule.{u, v} A)
    (N : CochainComplex (ModuleCat.{v} R) ℤ) (p q : ℤ)
    (m : M.X p) (f : (obj M N).X q) :
    (OfLeft.asCochain (obj M N) N ((evaluation M N).hom p m)).v
        q (p + q) (add_comm q p) f =
      ((p * q).negOnePow : R) • (asCochain M N f).v p (p + q) rfl m := sorry

end OfRight

end DifferentialGradedModule.InternalHom
