/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.DegreeZero
public import ReasLib.Algebra.Homology.CochainDGAlgebra.TensorProduct
public import ReasLib.Algebra.Homology.CochainDGAlgebra.Ulift
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.ChangeOfRings
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Homotopy
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Ulift
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base Change of Differential Graded Modules

For an `R`-algebra `S`, this file constructs the ordinary base change `M ⊗[R] S` of a
right differential graded `A`-module as a right module over `A ⊗[R] S`.  The action is the
Koszul action on the total tensor complex.  It also owns the canonical comparison with relative
tensor extension along `A ⟶ A ⊗[R] S`.  The primary construction uses the common carrier
`max uA uS`; an explicit `DifferentialGradedModule.ulift` transport is a separate bridge and
can be used only when its resulting carrier matches this boundary.
-/

@[expose] public section

noncomputable section

universe uR uS uA

open CategoryTheory
open ComplexShape DifferentialGradedCategory HomologicalComplex
open scoped DifferentialGradedCategory TensorProduct

namespace DifferentialGradedModule.BaseChange

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] [Algebra R S]
variable {A : CochainDGAlgebra.{uR, uA} R}

/-- The coefficient ring `S`, regarded as a cochain DGA over `R` concentrated in degree zero. -/
abbrev coefficients : CochainDGAlgebra.{uR, uS} R :=
  CochainDGAlgebra.ofAlgebra R S

/-- The base-changed cochain DGA `A ⊗[R] S`. -/
abbrev algebra (A : CochainDGAlgebra.{uR, uA} R) : CochainDGAlgebra.{uR, max uA uS} R :=
  CochainDGAlgebra.tensorProduct A (coefficients (R := R) (S := S))

/-- The total tensor complex underlying ordinary base change of `M`. -/
abbrev complex (M : DifferentialGradedModule.{uR, max uA uS} A) :
    CochainComplex (ModuleCat.{max uA uS} R) ℤ :=
  HomologicalComplex.mapBifunctor M.toCochainComplex
    (coefficients (R := R) (S := S)).toCochainComplex
    (CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (up ℤ)

/-- Include one homogeneous module-coefficient tensor summand in a total base-change degree. -/
abbrev summandInclusion (M : DifferentialGradedModule.{uR, max uA uS} A)
    (p q n : ℤ) (h : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
        ((coefficients (R := R) (S := S)).X q) ⟶
      (complex (S := S) M).X n :=
  ιMapBifunctor M.toCochainComplex
    (coefficients (R := R) (S := S)).toCochainComplex
    (CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (up ℤ) p q n h

/-- The homogeneous right `A`-action, bundled as a morphism from a module tensor product. -/
abbrev moduleActionHom (M : DifferentialGradedModule.{uR, max uA uS} A)
    (p i : ℤ) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p) (A.X i) ⟶ M.X (p + i) :=
  ModuleCat.TensorProduct.lift R (M.smul p i)

/-- The four-factor Koszul shuffle for a module term, a coefficient term, an algebra term,
and a second coefficient term. -/
def actionShuffle (M : DifferentialGradedModule.{uR, max uA uS} A)
    (p q i j : ℤ) :
    CochainDGAlgebra.Tensor.baseTensor (R := R)
        (CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
          ((coefficients (R := R) (S := S)).X q))
        (CochainDGAlgebra.Tensor.baseTensor (R := R) (A.X i)
          ((coefficients (R := R) (S := S)).X j)) ⟶
      CochainDGAlgebra.Tensor.baseTensor (R := R)
        (CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p) (A.X i))
        (CochainDGAlgebra.Tensor.baseTensor (R := R)
          ((coefficients (R := R) (S := S)).X q)
          ((coefficients (R := R) (S := S)).X j)) :=
  ModuleCat.TensorProduct.koszulShuffle R
    (M.X p) ((coefficients (R := R) (S := S)).X q) (A.X i)
    ((coefficients (R := R) (S := S)).X j) q i

/-- The Koszul action on four fixed homogeneous summands. -/
def actionComponent (M : DifferentialGradedModule.{uR, max uA uS} A)
    (p q i j : ℤ) :
    CochainDGAlgebra.Tensor.baseTensor (R := R)
        (CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
          ((coefficients (R := R) (S := S)).X q))
        (CochainDGAlgebra.Tensor.baseTensor (R := R) (A.X i)
          ((coefficients (R := R) (S := S)).X j)) ⟶
      (complex (S := S) M).X ((p + q) + (i + j)) :=
  actionShuffle (S := S) M p q i j ≫
    ModuleCat.TensorProduct.map R (moduleActionHom M p i)
      (CochainDGAlgebra.Tensor.mulHom (coefficients (R := R) (S := S)) q j) ≫
    summandInclusion (S := S) M (p + i) (q + j) ((p + q) + (i + j))
      (CochainDGAlgebra.Tensor.mulTotalDegree p q i j)

/-- On homogeneous pure tensors, the base-change action uses the Koszul sign obtained by
moving the coefficient of the module factor past the algebra factor. -/
theorem actionComponent_tmul
    (M : DifferentialGradedModule.{uR, max uA uS} A) (p q i j : ℤ)
    (x : M.X p) (s : (coefficients (R := R) (S := S)).X q)
    (a : A.X i) (t : (coefficients (R := R) (S := S)).X j) :
    (actionComponent (S := S) M p q i j).hom
        ((x ⊗ₜ[R] s) ⊗ₜ[R] (a ⊗ₜ[R] t)) =
      ((q * i).negOnePow : R) •
        (summandInclusion (S := S) M (p + i) (q + j) ((p + q) + (i + j))
          (CochainDGAlgebra.Tensor.mulTotalDegree p q i j)).hom
          (M.smul p i x a ⊗ₜ[R]
            (coefficients (R := R) (S := S)).mul q j s t) := sorry

/-- The fixed-summand base-change action, curried as a bilinear map. -/
abbrev actionCurried (M : DifferentialGradedModule.{uR, max uA uS} A)
    (p q i j : ℤ) :
    (CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
        ((coefficients (R := R) (S := S)).X q) : Type (max uA uS)) →ₗ[R]
      (CochainDGAlgebra.Tensor.baseTensor (R := R) (A.X i)
          ((coefficients (R := R) (S := S)).X j) : Type (max uA uS)) →ₗ[R]
        (complex (S := S) M).X ((p + q) + (i + j)) :=
  _root_.TensorProduct.curry (actionComponent (S := S) M p q i j).hom

/-- The targets of a fixed homogeneous action summand agree after total-degree transport. -/
theorem actionTargetEq
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n m p q : ℤ)
    (hpq : p + q = n) (i j : ℤ)
    (hij : (up ℤ).π (up ℤ) (up ℤ) (i, j) = m) :
    (complex (S := S) M).X ((p + q) + (i + j)) =
      (complex (S := S) M).X (n + m) := sorry

/-- Right action by a fixed element of one base-change tensor summand. -/
def rightActionComponent
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n m p q : ℤ)
    (hpq : p + q = n)
    (x : CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
      ((coefficients (R := R) (S := S)).X q)) (i j : ℤ)
    (hij : (up ℤ).π (up ℤ) (up ℤ) (i, j) = m) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (A.X i)
        ((coefficients (R := R) (S := S)).X j) ⟶
      (complex (S := S) M).X (n + m) :=
  ModuleCat.ofHom (actionCurried (S := S) M p q i j x) ≫
    eqToHom (actionTargetEq (S := S) M n m p q hpq i j hij)

/-- The right action descended from all summands in the algebra input. -/
def rightActionDesc
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n m p q : ℤ)
    (hpq : p + q = n)
    (x : CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
      ((coefficients (R := R) (S := S)).X q)) :
    (algebra (S := S) A).X m ⟶ (complex (S := S) M).X (n + m) :=
  mapBifunctorDesc
    (K₁ := A.toCochainComplex)
    (K₂ := (coefficients (R := R) (S := S)).toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (c := up ℤ)
    (rightActionComponent (S := S) M n m p q hpq x)

/-- Descended right action is additive in the fixed module input. -/
theorem rightActionDesc_add
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n m p q : ℤ)
    (hpq : p + q = n)
    (x y : CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
      ((coefficients (R := R) (S := S)).X q)) :
    (rightActionDesc (S := S) M n m p q hpq (x + y)).hom =
      (rightActionDesc (S := S) M n m p q hpq x).hom +
        (rightActionDesc (S := S) M n m p q hpq y).hom := sorry

/-- Descended right action is linear in the fixed module input. -/
theorem rightActionDesc_smul
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n m p q : ℤ)
    (hpq : p + q = n) (r : R)
    (x : CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
      ((coefficients (R := R) (S := S)).X q)) :
    (rightActionDesc (S := S) M n m p q hpq (r • x)).hom =
      r • (rightActionDesc (S := S) M n m p q hpq x).hom := sorry

/-- The base-change action on one summand of the module input. -/
def actionOnSummand
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n m p q : ℤ)
    (hpq : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
        ((coefficients (R := R) (S := S)).X q) ⟶
      ModuleCat.of R ((algebra (S := S) A).X m →ₗ[R]
        (complex (S := S) M).X (n + m)) :=
  ModuleCat.ofHom
    { toFun := fun x ↦ (rightActionDesc (S := S) M n m p q hpq x).hom
      map_add' := rightActionDesc_add (S := S) M n m p q hpq
      map_smul' := rightActionDesc_smul (S := S) M n m p q hpq }

/-- The Koszul right action of `A ⊗[R] S` on the total tensor complex `M ⊗[R] S`. -/
def action (M : DifferentialGradedModule.{uR, max uA uS} A) (n m : ℤ) :
    (complex (S := S) M).X n →ₗ[R] (algebra (S := S) A).X m →ₗ[R]
      (complex (S := S) M).X (n + m) :=
  (mapBifunctorDesc
    (K₁ := M.toCochainComplex)
    (K₂ := (coefficients (R := R) (S := S)).toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (c := up ℤ)
    (actionOnSummand (S := S) M n m)).hom

/-- Ordinary base change of a right DG `A`-module to a right DG `A ⊗[R] S`-module. -/
@[stacks 0BYZ "ordinary base change of a differential graded module"]
def obj (M : DifferentialGradedModule.{uR, max uA uS} A) :
    DifferentialGradedModule.{uR, max uA uS} (algebra (S := S) A) where
  X := (complex (S := S) M).X
  d n := ((complex (S := S) M).d n (n + 1)).hom
  smul := action (S := S) M
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The complex underlying ordinary DG-module base change is the total tensor complex. -/
@[simp]
theorem obj_toCochainComplex
    (M : DifferentialGradedModule.{uR, max uA uS} A) :
    (obj (S := S) M).toCochainComplex = complex (S := S) M := sorry

/-- The degree-`n` carrier of ordinary base change is the corresponding total tensor term. -/
@[simp]
theorem obj_X (M : DifferentialGradedModule.{uR, max uA uS} A) (n : ℤ) :
    (obj (S := S) M).X n = (complex (S := S) M).X n := sorry

/-- Applying a degree-`k` homogeneous map in the module factor changes total degree by `k`. -/
theorem mapDegree (p q n k : ℤ) (h : p + q = n) :
    (p + k) + q = n + k := sorry

/-- Apply a homogeneous module map to one pure summand of a base-change complex. -/
def mapPure {M N : DifferentialGradedModule.{uR, max uA uS} A} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom A M N k)
    (n p q : ℤ) (h : p + q = n) (x : M.X p)
    (s : (coefficients (R := R) (S := S)).X q) :
    (complex (S := S) N).X (n + k) :=
  (summandInclusion (S := S) N (p + k) q (n + k)
    (mapDegree p q n k h)).hom (f p x ⊗ₜ[R] s)

/-- The summand map induced by a homogeneous map in the module factor. -/
def mapComponent {M N : DifferentialGradedModule.{uR, max uA uS} A} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom A M N k)
    (n p q : ℤ) (h : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
        ((coefficients (R := R) (S := S)).X q) ⟶
      (complex (S := S) N).X (n + k) :=
  ModuleCat.TensorProduct.lift R
    (LinearMap.mk₂ R (mapPure (S := S) f n p q h) sorry sorry sorry sorry)

/-- The homogeneous map on total base-change complexes. -/
def mapLinear {M N : DifferentialGradedModule.{uR, max uA uS} A} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom A M N k) (n : ℤ) :
    (complex (S := S) M).X n →ₗ[R] (complex (S := S) N).X (n + k) :=
  (mapBifunctorDesc
    (K₁ := M.toCochainComplex)
    (K₂ := (coefficients (R := R) (S := S)).toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ mapComponent (S := S) f n p q h)).hom

/-- Ordinary base change of a homogeneous DG-module map. -/
def map {M N : DifferentialGradedModule.{uR, max uA uS} A} {k : ℤ}
    (f : DifferentialGradedModule.GradedHom A M N k) :
    DifferentialGradedModule.GradedHom (algebra (S := S) A)
      (obj (S := S) M) (obj (S := S) N) k :=
  ⟨mapLinear (S := S) f, sorry⟩

/-- Base change sends a pure tensor to the tensor of the mapped first factor. -/
theorem map_tmul {M N : DifferentialGradedModule.{uR, max uA uS} A}
    {k p q : ℤ}
    (f : DifferentialGradedModule.GradedHom A M N k) (x : M.X p)
    (s : (coefficients (R := R) (S := S)).X q) :
    map (S := S) f (p + q)
        ((summandInclusion (S := S) M p q (p + q) rfl).hom
          (x ⊗ₜ[R] s)) =
      cast (congrArg (fun n : ℤ ↦
        ((complex (S := S) N).X n : Type (max uA uS)))
        (mapDegree p q (p + q) k rfl))
        ((summandInclusion (S := S) N (p + k) q ((p + k) + q) rfl).hom
          (f p x ⊗ₜ[R] s)) := sorry

/-- Ordinary base change is a differential graded functor. -/
@[stacks 0BYZ "ordinary base-change DG functor"]
def dgFunctor (A : CochainDGAlgebra.{uR, uA} R) :
    DgFunctor R (DifferentialGradedModule.{uR, max uA uS} A)
      (DifferentialGradedModule.{uR, max uA uS} (algebra (S := S) A)) where
  obj := obj (S := S)
  map := map (S := S)
  map_add := sorry
  map_smul := sorry
  map_d := sorry
  map_id := sorry
  map_comp := sorry

/-- The DGA map used for relative tensor extension to `A ⊗[R] S`. -/
abbrev algebraMap (A : CochainDGAlgebra.{uR, uA} R) :
    CochainDGAlgebra.Hom A (algebra (S := S) A) :=
  CochainDGAlgebra.Tensor.leftFactorHom A (coefficients (R := R) (S := S))

/-- The canonical extension-of-scalars bimodule for `A ⟶ A ⊗[R] S`. -/
abbrev extension (A : CochainDGAlgebra.{uR, uA} R) :
    DifferentialGradedBimodule A (algebra (S := S) A) :=
  DifferentialGradedBimodule.ChangeOfRings.extension (algebraMap (S := S) A)

/-- The canonical comparison sends `x ⊗ s` to `x ⊗ (1 ⊗ s)`. -/
def comparisonPure (M : DifferentialGradedModule.{uR, max uA uS} A)
    (p q : ℤ) (x : M.X p) (s : (coefficients (R := R) (S := S)).X q) :
    DifferentialGradedBimodule.Tensor.family M (extension (S := S) A) (p + q) :=
  DifferentialGradedBimodule.Tensor.tmul M (extension (S := S) A) x
    (CochainDGAlgebra.Tensor.rightFactor A (coefficients (R := R) (S := S)) s)

/-- The canonical comparison on one homogeneous tensor summand. -/
def comparisonComponent
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n p q : ℤ)
    (h : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (M.X p)
        ((coefficients (R := R) (S := S)).X q) ⟶
      (DifferentialGradedBimodule.Tensor.obj M (extension (S := S) A)).X n :=
  ModuleCat.TensorProduct.lift R
    (LinearMap.mk₂ R
      (fun x s ↦ cast (congrArg (fun k : ℤ ↦
        ((DifferentialGradedBimodule.Tensor.obj M (extension (S := S) A)).X k :
          Type (max uA uS))) h)
        (comparisonPure (S := S) M p q x s)) sorry sorry sorry sorry)

/-- The degreewise linear map underlying the canonical base-change comparison. -/
def comparisonLinear
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n : ℤ) :
    (obj (S := S) M).X n →ₗ[R]
      (DifferentialGradedBimodule.Tensor.obj M (extension (S := S) A)).X n :=
  (mapBifunctorDesc
    (K₁ := M.toCochainComplex)
    (K₂ := (coefficients (R := R) (S := S)).toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ comparisonComponent (S := S) M n p q h)).hom

/-- The canonical DG-module comparison
`M ⊗[R] S ⟶ M ⊗_A (A ⊗[R] S)`. -/
@[stacks 0BYZ "ordinary base change to relative tensor comparison"]
def comparison (M : DifferentialGradedModule.{uR, max uA uS} A) :
    obj (S := S) M ⟶
      DifferentialGradedBimodule.Tensor.obj M (extension (S := S) A) where
  hom := comparisonLinear (S := S) M
  comm_d := sorry
  comm_smul := sorry

/-- The canonical comparison evaluates on a homogeneous pure tensor by inserting the unit of
`A` in the base-changed algebra factor. -/
@[simp, stacks 0BYZ "ordinary base-change comparison on pure tensors"]
theorem comparison_tmul
    (M : DifferentialGradedModule.{uR, max uA uS} A) (p q : ℤ)
    (x : M.X p) (s : (coefficients (R := R) (S := S)).X q) :
    (comparison (S := S) M).hom (p + q)
        ((summandInclusion (S := S) M p q (p + q) rfl).hom (x ⊗ₜ[R] s)) =
      comparisonPure (S := S) M p q x s := sorry

/-- The ordinary base-change comparison is an isomorphism. -/
@[stacks 0BYZ "invertibility of the ordinary base-change comparison"]
theorem comparison_isIso
    (M : DifferentialGradedModule.{uR, max uA uS} A) :
    IsIso (comparison (S := S) M) := sorry

/-- The map `x ↦ x ⊗ 1` into ordinary base change, in each homogeneous degree. -/
def comparisonUnit (M : DifferentialGradedModule.{uR, max uA uS} A) (p : ℤ) :
    M.X p →ₗ[R] (obj (S := S) M).X p :=
  (summandInclusion (S := S) M p 0 p (add_zero p)).hom.comp
    ((_root_.TensorProduct.mk R (M.X p)
      ((coefficients (R := R) (S := S)).X 0)).flip
        (coefficients (R := R) (S := S)).one)

/-- On an unbalanced homogeneous summand, the inverse comparison is
`x ⊗ b ↦ (x ⊗ 1) · b`, followed by total-degree reindexing. -/
def comparisonInvComponent
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n p q : ℤ)
    (h : p + q = n) :
    DifferentialGradedModule.TensorProduct.baseTensor (R := R) (M.X p)
        ((extension (S := S) A).X q) ⟶ (obj (S := S) M).X n :=
  ModuleCat.TensorProduct.lift R
      ((action (S := S) M p q).comp (comparisonUnit (S := S) M p)) ≫
    eqToHom (congrArg (fun k : ℤ ↦ (obj (S := S) M).X k) h)

/-- The explicit inverse comparison before imposing the homogeneous `A`-balancing relations. -/
def comparisonInvRawLinear
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n : ℤ) :
    DifferentialGradedBimodule.Tensor.rawTerm M (extension (S := S) A) n →ₗ[R]
      (obj (S := S) M).X n :=
  (mapBifunctorDesc
    (K₁ := DifferentialGradedBimodule.Tensor.leftComplex M)
    (K₂ := DifferentialGradedBimodule.Tensor.rightComplex (extension (S := S) A))
    (F := DifferentialGradedModule.TensorProduct.baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ comparisonInvComponent (S := S) M n p q h)).hom

/-- Descend `x ⊗ b ↦ (x ⊗ 1) · b` through the balancing quotient. -/
def comparisonInvLinear
    (M : DifferentialGradedModule.{uR, max uA uS} A) (n : ℤ) :
    (DifferentialGradedBimodule.Tensor.obj M (extension (S := S) A)).X n →ₗ[R]
      (obj (S := S) M).X n :=
  (DifferentialGradedBimodule.Tensor.relations M (extension (S := S) A) n).liftQ
    (comparisonInvRawLinear (S := S) M n) sorry

/-- The explicit inverse of the ordinary-to-relative base-change comparison. -/
def comparisonInv (M : DifferentialGradedModule.{uR, max uA uS} A) :
    DifferentialGradedBimodule.Tensor.obj M (extension (S := S) A) ⟶
      obj (S := S) M where
  hom := comparisonInvLinear (S := S) M
  comm_d := sorry
  comm_smul := sorry

/-- The inverse comparison on homogeneous relative pure tensors. -/
@[simp]
theorem comparisonInv_tmul
    (M : DifferentialGradedModule.{uR, max uA uS} A) (p q : ℤ)
    (x : M.X p) (b : (extension (S := S) A).X q) :
    (comparisonInv (S := S) M).hom (p + q)
        (DifferentialGradedBimodule.Tensor.tmul M (extension (S := S) A) x b) =
      action (S := S) M p q (comparisonUnit (S := S) M p x) b := sorry

/-- Ordinary ground-ring base change and relative tensor extension are canonically isomorphic. -/
@[stacks 0BYZ "ordinary and relative base-change isomorphism"]
noncomputable def comparisonIso
    (M : DifferentialGradedModule.{uR, max uA uS} A) :
    obj (S := S) M ≅
      DifferentialGradedBimodule.Tensor.obj M (extension (S := S) A) where
  hom := comparison (S := S) M
  inv := comparisonInv (S := S) M
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `comparisonIso` is the canonical ordinary-to-relative comparison. -/
@[simp, stacks 0BYZ "forward map of the ordinary base-change comparison isomorphism"]
theorem comparisonIso_hom
    (M : DifferentialGradedModule.{uR, max uA uS} A) :
    (comparisonIso (S := S) M).hom = comparison (S := S) M := sorry

/-- The inverse map of `comparisonIso` is the canonical inverse of the comparison morphism. -/
@[simp, stacks 0BYZ "inverse map of the ordinary base-change comparison isomorphism"]
theorem comparisonIso_inv
    (M : DifferentialGradedModule.{uR, max uA uS} A) :
    (comparisonIso (S := S) M).inv =
      @inv _ _ _ _ (comparison (S := S) M) (comparison_isIso (S := S) M) := sorry

/-- The comparison in the DG homotopy category. -/
@[stacks 0BYZ "component of the homotopy base-change comparison"]
noncomputable def comparisonKApp
    (M : K R (DifferentialGradedModule.{uR, max uA uS} A)) :
    ((dgFunctor (S := S) A).mapK).obj M ≅
      ((DifferentialGradedBimodule.Tensor.dgFunctor (extension (S := S) A)).mapK).obj M :=
  (DifferentialGradedModule.toK (algebra (S := S) A)).mapIso
    (comparisonIso (S := S) M.obj)

/-- Ordinary base change is naturally isomorphic on homotopy categories to tensor extension
along `A ⟶ A ⊗[R] S`. -/
@[stacks 0BYZ "ordinary and relative DG base change"]
noncomputable def comparisonK (A : CochainDGAlgebra.{uR, uA} R) :
    (dgFunctor (S := S) A).mapK ≅
      (DifferentialGradedBimodule.Tensor.dgFunctor (extension (S := S) A)).mapK :=
  NatIso.ofComponents (comparisonKApp (S := S)) (fun _ ↦ sorry)

/-- The forward component of `comparisonK` is the explicit comparison isomorphism. -/
@[simp, stacks 0BYZ "forward component of the homotopy base-change comparison"]
theorem comparisonK_hom_app (A : CochainDGAlgebra.{uR, uA} R)
    (M : K R (DifferentialGradedModule.{uR, max uA uS} A)) :
    (comparisonK (S := S) A).hom.app M = (comparisonKApp (S := S) M).hom := sorry

/-- The inverse component of `comparisonK` is the inverse of the explicit comparison isomorphism. -/
@[simp, stacks 0BYZ "inverse component of the homotopy base-change comparison"]
theorem comparisonK_inv_app (A : CochainDGAlgebra.{uR, uA} R)
    (M : K R (DifferentialGradedModule.{uR, max uA uS} A)) :
    (comparisonK (S := S) A).inv.app M = (comparisonKApp (S := S) M).inv := sorry

end DifferentialGradedModule.BaseChange
