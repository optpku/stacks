/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Scalar
public import ReasLib.Algebra.Homology.DifferentialGradedModule.BaseChange
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of scalars for ordinary DG base change

This file gives the concrete comparison behind the restriction-of-scalars square for base
change.  Its components are defined on homogeneous pure tensors, before passing to homotopy or
derived categories.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory
open ComplexShape DifferentialGradedCategory HomologicalComplex
open scoped DifferentialGradedCategory TensorProduct

namespace DifferentialGradedModule.BaseChange

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable {A : CochainDGAlgebra.{u, u} R}

/-- The right-factor map `S ⟶ A ⊗[R] S` used to forget a base-changed module to an
`S`-module. -/
abbrev coefficientMap (A : CochainDGAlgebra.{u, u} R) :
    CochainDGAlgebra.Hom (coefficients (R := R) (S := S)) (algebra (S := S) A) :=
  CochainDGAlgebra.Tensor.rightFactorHom A (coefficients (R := R) (S := S))

/-- The canonical map from the ground ring DGA to a cochain DGA. -/
abbrev groundMap (A : CochainDGAlgebra.{u, u} R) :
    CochainDGAlgebra.Hom (CochainDGAlgebra.ofAlgebra R R) A :=
  CochainDGAlgebra.Hom.fromBase A

/-- The extension bimodule for the coefficient map `R ⟶ S`, both regarded as degree-zero
cochain DGAs over `R`. -/
abbrev coefficientExtension :
    DifferentialGradedBimodule (CochainDGAlgebra.ofAlgebra R R)
      (coefficients (R := R) (S := S)) :=
  DifferentialGradedBimodule.ChangeOfRings.extension
    (groundMap (coefficients (R := R) (S := S)))

/-- The two canonical maps from the ground-ring DGA to `A ⊗[R] S` agree. -/
@[stacks 0BYZ "commutative DGA square underlying base change"]
theorem algebraMap_comp_groundMap (A : CochainDGAlgebra.{u, u} R) :
    CochainDGAlgebra.Hom.comp (algebraMap (S := S) A) (groundMap A) =
      CochainDGAlgebra.Hom.comp (coefficientMap (S := S) A)
        (groundMap (coefficients (R := R) (S := S))) := sorry

/-- Base change followed by restriction along `S ⟶ A ⊗[R] S`. -/
abbrev restrictedObj (M : DifferentialGradedModule A) :
    DifferentialGradedModule (coefficients (R := R) (S := S)) :=
  (coefficientMap (S := S) A).restrictModule (obj (S := S) M)

/-- Forgetting an `A`-module to `R` and then extending scalars from `R` to `S`. -/
abbrev extendedObj (M : DifferentialGradedModule A) :
    DifferentialGradedModule (coefficients (R := R) (S := S)) :=
  DifferentialGradedBimodule.Tensor.obj ((groundMap A).restrictModule M)
    (coefficientExtension (R := R) (S := S))

/-- The pure-tensor value of the comparison between the two ordinary scalar-change paths. -/
def restrictionComparisonPure (M : DifferentialGradedModule A)
    (p q : ℤ) (x : M.X p) (s : (coefficients (R := R) (S := S)).X q) :
    DifferentialGradedBimodule.Tensor.family ((groundMap A).restrictModule M)
      (coefficientExtension (R := R) (S := S)) (p + q) :=
  DifferentialGradedBimodule.Tensor.tmul ((groundMap A).restrictModule M)
    (coefficientExtension (R := R) (S := S)) x s

/-- The ordinary restriction comparison on one homogeneous tensor summand. -/
def restrictionComparisonComponent (M : DifferentialGradedModule A) (n p q : ℤ)
    (h : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
        ((coefficients (R := R) (S := S)).X q) ⟶
      (extendedObj (S := S) M).X n :=
  summandInclusion (S := S) M p q n h ≫
    ModuleCat.ofHom (DifferentialGradedBimodule.Tensor.mk
      ((groundMap A).restrictModule M) (coefficientExtension (R := R) (S := S)) n)

/-- The degreewise linear map underlying the ordinary restriction comparison. -/
def restrictionComparisonLinear (M : DifferentialGradedModule A) (n : ℤ) :
    (restrictedObj (S := S) M).X n →ₗ[R] (extendedObj (S := S) M).X n :=
  (mapBifunctorDesc
    (K₁ := M.toCochainComplex)
    (K₂ := (coefficients (R := R) (S := S)).toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R))
    (c := ComplexShape.up ℤ)
    (fun p q h ↦ restrictionComparisonComponent (S := S) M n p q h)).hom

/-- The comparison is the quotient map from the common unbalanced tensor complex. -/
theorem restrictionComparisonLinear_eq_mk (M : DifferentialGradedModule A) (n : ℤ) :
    restrictionComparisonLinear (S := S) M n =
      DifferentialGradedBimodule.Tensor.mk ((groundMap A).restrictModule M)
        (coefficientExtension (R := R) (S := S)) n := by
  apply congrArg (fun f : (restrictedObj (S := S) M).X n ⟶
    (extendedObj (S := S) M).X n ↦ f.hom)
  apply mapBifunctor.hom_ext
  intro p q h
  exact ι_mapBifunctorDesc _ p q h

/-- The canonical ordinary comparison between the two paths in the scalar-restriction square. -/
@[stacks 0BYZ "ordinary restriction-of-scalars base-change comparison"]
def restrictionComparison (M : DifferentialGradedModule A) :
    restrictedObj (S := S) M ⟶ extendedObj (S := S) M where
  hom := restrictionComparisonLinear (S := S) M
  comm_d := sorry
  comm_smul := sorry

/-- The ordinary restriction comparison evaluates as the identity on homogeneous pure tensors. -/
@[simp]
theorem restrictionComparison_tmul (M : DifferentialGradedModule A)
    (p q : ℤ) (x : M.X p) (s : (coefficients (R := R) (S := S)).X q) :
    (restrictionComparison (S := S) M).hom (p + q)
        ((summandInclusion (S := S) M p q (p + q) rfl).hom (x ⊗ₜ[R] s)) =
      restrictionComparisonPure (S := S) M p q x s := by
  change restrictionComparisonLinear (S := S) M (p + q) _ = _
  rw [restrictionComparisonLinear_eq_mk]
  rfl

set_option maxHeartbeats 2000000 in
/-- Over the ground-ring DGA, the balancing relations already vanish in the
ordinary tensor product over `R`. -/
theorem restrictionComparison_relations (M : DifferentialGradedModule A) (n : ℤ) :
    DifferentialGradedBimodule.Tensor.relations ((groundMap A).restrictModule M)
      (coefficientExtension (R := R) (S := S)) n ≤
        LinearMap.ker (LinearMap.id : (restrictedObj (S := S) M).X n →ₗ[R]
          (restrictedObj (S := S) M).X n) := by
  classical
  apply Submodule.span_le.mpr
  rintro z ⟨p, i, q, h, m, a, x, rfl⟩
  change DifferentialGradedBimodule.Tensor.balanceGenerator
    ((groundMap A).restrictModule M) (coefficientExtension (R := R) (S := S))
      p i q n h m a x = 0
  by_cases hi : i = 0
  · subst i
    let e := CochainDGAlgebra.ofAlgebraZeroIso R R
    let r : R := e.hom a
    have ha : a = r • (CochainDGAlgebra.ofAlgebra R R).one := by
      change a = r • e.inv (1 : R)
      rw [← map_smul, smul_eq_mul, mul_one]
      exact (e.hom_inv_id_apply a).symm
    rw [ha]
    dsimp only [DifferentialGradedBimodule.Tensor.balanceGenerator,
      DifferentialGradedModule.TensorProduct.balanceGenerator]
    have hm := ((groundMap A).restrictModule M).smul_one r p m
    have hx := (coefficientExtension (R := R) (S := S)).toLeftModule.smul_one r q x
    have cast_left (p p' q n : ℤ) (hp : p = p') (hpq : p' + q = n)
        (m : M.X p) (x : (coefficients (R := R) (S := S)).X q) :
        (summandInclusion (S := S) M p' q n hpq).hom
            (cast (congrArg (fun k : ℤ ↦ (M.X k : Type u)) hp) m ⊗ₜ[R] x) =
          (summandInclusion (S := S) M p q n (by rw [hp]; exact hpq)).hom
            (m ⊗ₜ[R] x) := by
      subst p'
      rfl
    have cast_right (p q q' n : ℤ) (hq : q = q') (hpq : p + q' = n)
        (m : M.X p) (x : (coefficients (R := R) (S := S)).X q) :
        (summandInclusion (S := S) M p q' n hpq).hom
            (m ⊗ₜ[R] cast (congrArg
              (fun k : ℤ ↦ ((coefficients (R := R) (S := S)).X k : Type u)) hq) x) =
          (summandInclusion (S := S) M p q n (by rw [hq]; exact hpq)).hom
            (m ⊗ₜ[R] x) := by
      subst q'
      rfl
    rw [hm, hx]
    change (summandInclusion (S := S) M (p + 0) q n h).hom
        (cast (congrArg (fun k : ℤ ↦ (M.X k : Type u)) (add_zero p).symm)
          (r • m) ⊗ₜ[R] x) -
      (summandInclusion (S := S) M p (0 + q) n
        (DifferentialGradedModule.TensorProduct.balanceRightDegree p 0 q n h)).hom
        (m ⊗ₜ[R] cast (congrArg
          (fun k : ℤ ↦ ((coefficients (R := R) (S := S)).X k : Type u))
          (zero_add q).symm) (r • x)) = 0
    rw [cast_left p (p + 0) q n (add_zero p).symm h,
      cast_right p q (0 + q) n (zero_add q).symm
        (DifferentialGradedModule.TensorProduct.balanceRightDegree p 0 q n h)]
    apply sub_eq_zero.mpr
    apply congrArg (fun z : (M.X p) ⊗[R] ((coefficients (R := R) (S := S)).X q) ↦
      (summandInclusion (S := S) M p q n (by simpa only [add_zero] using h)).hom z)
    exact TensorProduct.smul_tmul (R := R) (M := M.X p)
      (N := (coefficients (R := R) (S := S)).X q) r m x
  · haveI : Subsingleton ((CochainDGAlgebra.ofAlgebra R R).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp
        (isZero_single_obj_X (up ℤ) 0 (ModuleCat.of R R) i hi)
    have ha : a = 0 := Subsingleton.elim _ _
    simp only [DifferentialGradedBimodule.Tensor.balanceGenerator,
      DifferentialGradedModule.TensorProduct.balanceGenerator, ha, map_zero,
      LinearMap.zero_apply]
    change (summandInclusion (S := S) M (p + i) q n h).hom
        ((0 : M.X (p + i)) ⊗ₜ[R] x) -
      (summandInclusion (S := S) M p (i + q) n
        (DifferentialGradedModule.TensorProduct.balanceRightDegree p i q n h)).hom
        (m ⊗ₜ[R] (0 : (coefficients (R := R) (S := S)).X (i + q))) = 0
    erw [TensorProduct.zero_tmul, TensorProduct.tmul_zero]
    apply sub_eq_zero.mpr
    exact (map_zero (summandInclusion (S := S) M (p + i) q n h).hom).trans
      (map_zero (summandInclusion (S := S) M p (i + q) n
        (DifferentialGradedModule.TensorProduct.balanceRightDegree p i q n h)).hom).symm

/-- The inverse comparison sends the class of `x ⊗ s` to its summand in the
ordinary base-change complex.  It is the identity on the common raw tensor complex,
descended through the ground-ring balancing quotient. -/
def restrictionComparisonInvLinear (M : DifferentialGradedModule A) (n : ℤ) :
    (extendedObj (S := S) M).X n →ₗ[R] (restrictedObj (S := S) M).X n :=
  (DifferentialGradedBimodule.Tensor.relations ((groundMap A).restrictModule M)
    (coefficientExtension (R := R) (S := S)) n).liftQ LinearMap.id
      (restrictionComparison_relations (S := S) M n)

/-- Descending the identity and then applying the quotient map is the identity. -/
theorem restrictionComparisonLinear_inv (M : DifferentialGradedModule A) (n : ℤ)
    (x : (extendedObj (S := S) M).X n) :
    restrictionComparisonLinear (S := S) M n
      (restrictionComparisonInvLinear (S := S) M n x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    rw [restrictionComparisonLinear_eq_mk]
    rfl

/-- The quotient map followed by the descended identity is the identity. -/
theorem restrictionComparisonInvLinear_comparison (M : DifferentialGradedModule A) (n : ℤ)
    (x : (restrictedObj (S := S) M).X n) :
    restrictionComparisonInvLinear (S := S) M n
      (restrictionComparisonLinear (S := S) M n x) = x := by
  rw [restrictionComparisonLinear_eq_mk]
  rfl

/-- The inverse comparison commutes with the differential. -/
theorem restrictionComparisonInvLinear_comm_d (M : DifferentialGradedModule A)
    (n : ℤ) (x : (extendedObj (S := S) M).X n) :
    restrictionComparisonInvLinear (S := S) M (n + 1) ((extendedObj (S := S) M).d n x) =
      (restrictedObj (S := S) M).d n
        (restrictionComparisonInvLinear (S := S) M n x) := by
  have h := congrArg (restrictionComparisonInvLinear (S := S) M (n + 1))
    ((restrictionComparison (S := S) M).comm_d n
      (restrictionComparisonInvLinear (S := S) M n x))
  simpa only [restrictionComparison, restrictionComparisonLinear_inv,
    restrictionComparisonInvLinear_comparison] using h.symm

/-- The inverse comparison respects the coefficient-DGA action. -/
theorem restrictionComparisonInvLinear_comm_smul (M : DifferentialGradedModule A)
    (n i : ℤ) (x : (extendedObj (S := S) M).X n)
    (s : (coefficients (R := R) (S := S)).X i) :
    restrictionComparisonInvLinear (S := S) M (n + i)
        ((extendedObj (S := S) M).smul n i x s) =
      (restrictedObj (S := S) M).smul n i
        (restrictionComparisonInvLinear (S := S) M n x) s := by
  have h := congrArg (restrictionComparisonInvLinear (S := S) M (n + i))
    ((restrictionComparison (S := S) M).comm_smul n i
      (restrictionComparisonInvLinear (S := S) M n x) s)
  simpa only [restrictionComparison, restrictionComparisonLinear_inv,
    restrictionComparisonInvLinear_comparison] using h.symm

/-- The explicit inverse in the category of differential graded coefficient modules. -/
def restrictionComparisonInv (M : DifferentialGradedModule A) :
    extendedObj (S := S) M ⟶ restrictedObj (S := S) M where
  hom := restrictionComparisonInvLinear (S := S) M
  comm_d := restrictionComparisonInvLinear_comm_d (S := S) M
  comm_smul := restrictionComparisonInvLinear_comm_smul (S := S) M

/-- The canonical ordinary isomorphism between the two scalar-change paths. -/
noncomputable def restrictionComparisonIso (M : DifferentialGradedModule A) :
    restrictedObj (S := S) M ≅ extendedObj (S := S) M where
  hom := restrictionComparison (S := S) M
  inv := restrictionComparisonInv (S := S) M
  hom_inv_id := by
    apply DifferentialGradedModule.hom_ext
    intro n x
    exact restrictionComparisonInvLinear_comparison (S := S) M n x
  inv_hom_id := by
    apply DifferentialGradedModule.hom_ext
    intro n x
    exact restrictionComparisonLinear_inv (S := S) M n x

/-- The ordinary comparison between the two scalar-change paths is invertible. -/
theorem restrictionComparison_isIso (M : DifferentialGradedModule A) :
    IsIso (restrictionComparison (S := S) M) :=
  (restrictionComparisonIso (S := S) M).isIso_hom

/-- The homotopy-level path obtained by base change and then restriction to the coefficient
DGA. -/
abbrev restrictedKFunctor (A : CochainDGAlgebra.{u, u} R) :=
  (dgFunctor (S := S) A).mapK ⋙
    (coefficientMap (S := S) A).restrictDgFunctor.mapK

/-- The homotopy-level path obtained by restriction to the ground ring and extension to the
coefficient DGA. -/
abbrev extendedKFunctor (A : CochainDGAlgebra.{u, u} R) :=
  (groundMap A).restrictDgFunctor.mapK ⋙
    (DifferentialGradedBimodule.Tensor.dgFunctor
      (coefficientExtension (R := R) (S := S))).mapK

/-- The component of the ordinary restriction comparison in the DG homotopy category. -/
noncomputable def restrictionComparisonKApp
    (M : K R (DifferentialGradedModule.{u, u} A)) :
    (restrictedKFunctor (S := S) A).obj M ≅ (extendedKFunctor (S := S) A).obj M :=
  (DifferentialGradedModule.toK (coefficients (R := R) (S := S))).mapIso
    (restrictionComparisonIso (S := S) M.obj)

/-- The two ordinary scalar-change paths are naturally isomorphic on DG homotopy categories. -/
@[stacks 0BYZ "ordinary restriction-of-scalars square"]
noncomputable def restrictionComparisonK (A : CochainDGAlgebra.{u, u} R) :
    restrictedKFunctor (S := S) A ≅ extendedKFunctor (S := S) A :=
  NatIso.ofComponents (restrictionComparisonKApp (S := S)) (fun _ ↦ sorry)

end DifferentialGradedModule.BaseChange
