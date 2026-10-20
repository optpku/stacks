/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.FiniteEtale
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite field-fibre comparison for a prescribed closure embedding

Finite affine coordinates are evaluated in the given source field and descended
through the relative algebraic closure. The inverse uses the supplied embedding;
it does not select a preimage from an admitted finite-fibre bijection.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.GeometricPoint.FieldComparison

variable {k Ω : Type u} [Field k] [Field Ω] [Algebra k Ω] [IsAlgClosed Ω]
variable (ι : AlgebraicClosure k →ₐ[k] Ω)

/-- The prescribed closure embedding has algebraic values. -/
theorem embedding_mem (x : AlgebraicClosure k) :
    ι x ∈ algebraicClosure k Ω :=
  mem_algebraicClosure_iff'.mpr ((Algebra.IsIntegral.isIntegral x).map ι)

/-- Restrict the specified embedding to the relative algebraic closure. -/
def algebraicInclusion : AlgebraicClosure k →ₐ[k] algebraicClosure k Ω :=
  ι.codRestrict (algebraicClosure k Ω).toSubalgebra (embedding_mem ι)

/-- The prescribed embedding identifies the two algebraic closures by the native
algebraic Schroeder--Bernstein theorem. -/
def algebraicEquiv : AlgebraicClosure k ≃ₐ[k] algebraicClosure k Ω :=
  AlgEquiv.ofBijective (algebraicInclusion ι)
    (Algebra.IsAlgebraic.algHom_bijective₂ (algebraicInclusion ι)
      (IsAlgClosed.lift : algebraicClosure k Ω →ₐ[k] AlgebraicClosure k)).1

variable (Y : FiniteEtale (Spec (CommRingCat.of k)))

/-- Evaluate the actual finite affine coordinates at the supplied fibre point. -/
def pointEvaluation
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk Y.hom) :
    Γ(Y.left, ⊤) →+* Ω :=
  (y.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom

/-- Finiteness of the cover makes every evaluated coordinate algebraic over the base. -/
theorem pointEvaluation_mem
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk Y.hom)
    (r : Γ(Y.left, ⊤)) :
    pointEvaluation Y y r ∈ algebraicClosure k Ω := sorry

/-- Descend the evaluated coordinates using the inverse of the specified closure embedding. -/
def descendedEvaluation
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk Y.hom) :
    Γ(Y.left, ⊤) →+* AlgebraicClosure k :=
  (algebraicEquiv ι).symm.toRingHom.comp
    ((pointEvaluation Y y).codRestrict
      (algebraicClosure k Ω).toSubalgebra.toSubsemiring (pointEvaluation_mem Y y))

/-- Recover the algebraic-closure-valued fibre point from its descended affine coordinates. -/
def inverse
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk Y.hom) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) ⟶ Over.mk Y.hom := by
  let hfinite : AlgebraicGeometry.IsFinite Y.hom := Y.prop.1
  let haffine : IsAffineHom Y.hom := hfinite.toIsAffineHom
  let hbase : IsAffine ((Functor.fromPUnit (Spec (CommRingCat.of k))).obj Y.right) := by
    change IsAffine (Spec (CommRingCat.of k))
    infer_instance
  letI : IsAffine Y.left := @isAffine_of_isAffineHom _ _ Y.hom haffine hbase
  exact Over.homMk
    (Spec.map (CommRingCat.ofHom (descendedEvaluation ι Y y)) ≫ Y.left.isoSpec.inv)
    (w := sorry)

/-- Extend a fibre point along the supplied closure embedding. -/
def forward
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) ⟶ Over.mk Y.hom) :
    Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk Y.hom :=
  Over.homMk (Spec.map (CommRingCat.ofHom ι.toRingHom) ≫ y.left) (w := sorry)

/-- The finite-fibre equivalence has its prescribed forward and coordinate inverse functions. -/
def equiv :
    (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) ⟶ Over.mk Y.hom) ≃
      (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk Y.hom) where
  toFun := forward ι Y
  invFun := inverse ι Y
  left_inv := sorry
  right_inv := sorry

@[simp]
theorem equiv_apply
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))) ⟶ Over.mk Y.hom) :
    equiv ι Y y = forward ι Y y := rfl

@[simp]
theorem equiv_symm_apply
    (y : Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k Ω))) ⟶ Over.mk Y.hom) :
    (equiv ι Y).symm y = inverse ι Y y := rfl

end AlgebraicGeometry.Scheme.GeometricPoint.FieldComparison
