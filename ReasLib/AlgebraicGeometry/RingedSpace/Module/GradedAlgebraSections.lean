/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Commutative

/-!
# Graded global sections of an algebra sheaf

The nonnegative homogeneous global sections of an integer-graded algebra sheaf form an
externally graded ring. Its internal homogeneous summands give the grading used by projective
constructions.
-/

@[expose] public section

open CategoryTheory Opposite
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.GradedAlgebraSections

variable {X : RingedSpace.{u}}
variable (𝒜 : GradedAlgebraSheaf.{u, u} X.sheaf)

/-- The global sections of the nonnegative homogeneous piece of degree `n`. -/
abbrev degree (n : ℕ) : Type u :=
  ↥((𝒜 (n : ℤ)).val.obj (op ⊤))

/-- The external direct sum of the nonnegative homogeneous global sections. -/
abbrev ring : Type u :=
  ⨁ n : ℕ, degree 𝒜 n

/-- The unit section in degree zero. -/
instance instGOne : GradedMonoid.GOne (degree 𝒜) where
  one := 𝒜.one (op ⊤)

/-- Sectionwise multiplication supplies multiplication on homogeneous global sections. -/
instance instGNonUnitalNonAssocSemiring :
    DirectSum.GNonUnitalNonAssocSemiring (degree 𝒜) where
  mul := fun {m n} x y ↦ 𝒜.mul (op ⊤) (m : ℤ) (n : ℤ) x y
  mul_zero := sorry
  zero_mul := sorry
  mul_add := sorry
  add_mul := sorry

/-- The homogeneous global sections inherit the graded monoid laws of the algebra sheaf. -/
instance instGMonoid : GradedMonoid.GMonoid (degree 𝒜) where
  toGMul := inferInstance
  toGOne := inferInstance
  one_mul := sorry
  mul_one := sorry
  mul_assoc := sorry
  gnpow_zero' := sorry
  gnpow_succ' := sorry

/-- Homogeneous global sections of an ordinarily commutative algebra sheaf commute. -/
instance instGCommMonoid [𝒜.IsCommutative] :
    GradedMonoid.GCommMonoid (degree 𝒜) where
  toGMonoid := inferInstance
  mul_comm := sorry

/-- Degree-zero global sections supply the natural-number casts of the graded section ring. -/
instance instGSemiring : DirectSum.GSemiring (degree 𝒜) :=
  { (inferInstance : DirectSum.GNonUnitalNonAssocSemiring (degree 𝒜)),
    (inferInstance : GradedMonoid.GMonoid (degree 𝒜)) with
    natCast := fun n ↦ n • 𝒜.one (op ⊤)
    natCast_zero := sorry
    natCast_succ := sorry }

/-- Degree-zero global sections supply the integer casts of the graded section ring. -/
instance instGRing : DirectSum.GRing (degree 𝒜) :=
  { (inferInstance : DirectSum.GSemiring (degree 𝒜)) with
    intCast := fun z ↦ z • 𝒜.one (op ⊤)
    intCast_ofNat := sorry
    intCast_negSucc_ofNat := sorry }

/-- The global-section ring of an ordinarily commutative algebra sheaf is a graded commutative
semiring. -/
instance instGCommSemiring [𝒜.IsCommutative] :
    DirectSum.GCommSemiring (degree 𝒜) :=
  { (inferInstance : DirectSum.GSemiring (degree 𝒜)),
    (inferInstance : GradedMonoid.GCommMonoid (degree 𝒜)) with }

/-- The global-section ring of an ordinarily commutative algebra sheaf is a graded commutative
ring. -/
instance instGCommRing [𝒜.IsCommutative] : DirectSum.GCommRing (degree 𝒜) :=
  { (inferInstance : DirectSum.GRing (degree 𝒜)),
    (inferInstance : DirectSum.GCommSemiring (degree 𝒜)) with }

/-- The internal degree-`n` summand of the direct sum of homogeneous global sections. -/
def grading (n : ℕ) : AddSubgroup (ring 𝒜) where
  carrier := Set.range (DirectSum.of (degree 𝒜) n)
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- An external homogeneous piece is additively equivalent to its internal summand. -/
def gradeEquiv (n : ℕ) : degree 𝒜 n ≃+ grading 𝒜 n where
  toFun := fun x ↦ ⟨DirectSum.of (degree 𝒜) n x, ⟨x, rfl⟩⟩
  invFun := fun x ↦ Classical.choose x.2
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The forward map of `gradeEquiv` is the canonical direct-sum inclusion. -/
@[simp]
theorem gradeEquiv_apply (n : ℕ) (x : degree 𝒜 n) :
    ((gradeEquiv 𝒜 n x : grading 𝒜 n) : ring 𝒜) = DirectSum.of (degree 𝒜) n x := sorry

/-- The additive decomposition map into the internal homogeneous summands. -/
def decompose : ring 𝒜 →+ ⨁ n : ℕ, grading 𝒜 n :=
  (DirectSum.congrAddEquiv (gradeEquiv 𝒜)).toAddMonoidHom

/-- The internal summands contain the unit and are closed under multiplication. -/
instance instSetLikeGradedMonoid : SetLike.GradedMonoid (grading 𝒜) where
  toGradedOne := { one_mem := sorry }
  toGradedMul := { mul_mem := sorry }

/-- The internal homogeneous summands form a direct-sum decomposition. -/
instance instDecomposition : DirectSum.Decomposition (grading 𝒜) where
  decompose' := decompose 𝒜
  left_inv := sorry
  right_inv := sorry

/-- The internal homogeneous summands give the global-section ring its natural grading. -/
instance instGradedRing : GradedRing (grading 𝒜) :=
  { (inferInstance : SetLike.GradedMonoid (grading 𝒜)),
    (inferInstance : DirectSum.Decomposition (grading 𝒜)) with }

end AlgebraicGeometry.RingedSpace.GradedAlgebraSections
