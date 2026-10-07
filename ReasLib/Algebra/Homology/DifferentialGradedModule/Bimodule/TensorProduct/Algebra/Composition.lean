module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Hom.Restriction
public import ReasLib.Algebra.Homology.CochainDGAlgebra.TensorProduct
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Algebra
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Composition
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular

/-!
# Composition of Algebra-Tensor DG Bimodules

This file owns the ordinary differential graded data underlying composition of the canonical
algebra-tensor bimodules.  It constructs the literal triple tensor, the balanced contraction of
the two middle algebra factors, and its images as bimodule, right-module, and homotopy-category
morphisms.  Derived comparison maps belong to the separate derived-composition layer.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open ComplexShape
open DifferentialGradedCategory
open HomologicalComplex
open scoped DifferentialGradedCategory TensorProduct

namespace DifferentialGradedBimodule.Tensor.AlgebraTensor

variable {R : Type u} [CommRing R]

/-- The right `B`-module `(A ⊗[R] B)_B`, viewed in the differential graded homotopy
category. -/
@[stacks 0BZ4 "homotopy object of the external tensor module"]
noncomputable abbrev rightOnK (A B : CochainDGAlgebra.{u, v} R) :
    K R (DifferentialGradedModule.{u, v} B) :=
  ⟨(algebra A B).toRightModule⟩

/-- The ordinary relative tensor of the two algebra-tensor bimodules occurring in
Equation 22.34.1.1. -/
@[stacks 0BZ4 "ordinary relative tensor of external tensor bimodules"]
noncomputable abbrev relativeModule (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v} C :=
  obj (algebra A B).toRightModule (algebra B C)

/-- The right-associated tensor DGA whose underlying complex is the literal ground-ring triple
tensor `A ⊗[R] (B ⊗[R] C)` (with `A.opposite` carrying the left action). -/
@[stacks 0BZ4 "right-associated algebra triple DGA"]
noncomputable abbrev tripleDGA (A B C : CochainDGAlgebra.{u, v} R) :
    CochainDGAlgebra.{u, v} R :=
  CochainDGAlgebra.tensorProduct A.opposite
    (CochainDGAlgebra.tensorProduct B C)

/-- The DGA map `A.opposite ⊗[R] C ⟶ A.opposite ⊗[R] (B ⊗[R] C)` that is the
identity on `A.opposite` and inserts the unit of `B` on the right. -/
@[stacks 0BZ4 "enveloping map for the algebra triple"]
noncomputable def tripleEnvelopingHom (A B C : CochainDGAlgebra.{u, v} R) :
    CochainDGAlgebra.Hom (CochainDGAlgebra.enveloping A C) (tripleDGA A B C) :=
  CochainDGAlgebra.Hom.tensorProduct (CochainDGAlgebra.Hom.id A.opposite)
    (CochainDGAlgebra.Tensor.rightFactorHom B C)

/-- The literal triple tensor `A ⊗[R] (B ⊗[R] C)` with its canonical differential
graded `(A, C)`-bimodule structure. -/
@[stacks 0BZ4 "ordinary algebra triple tensor bimodule"]
noncomputable def tripleBimodule (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedBimodule.{u, v, v, v} A C :=
  (tripleEnvelopingHom A B C).restrictModule
    (tripleDGA A B C).regularModule

/-- The literal ground-ring triple tensor `A ⊗[R] (B ⊗[R] C)` as a right differential
graded `C`-module. -/
@[stacks 0BZ4 "ordinary algebra triple tensor"]
noncomputable abbrev tripleRightModule (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v} C :=
  (tripleBimodule A B C).toRightModule

/-- The complex underlying `tripleRightModule A B C` is the literal right-associated
total tensor complex `A ⊗[R] (B ⊗[R] C)`. -/
@[stacks 0BZ4 "underlying complex of the ordinary algebra triple tensor"]
theorem tripleRightModule_toCochainComplex
    (A B C : CochainDGAlgebra.{u, v} R) :
    (tripleRightModule A B C).toCochainComplex =
      CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C) := sorry

/-- The degree-`n` carrier of `tripleRightModule A B C` is the degree-`n` term of the
literal total complex `A ⊗[R] (B ⊗[R] C)`. -/
@[stacks 0BZ4 "graded component of the algebra triple module"]
theorem tripleRightModule_X (A B C : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    (tripleRightModule A B C).X n =
      (CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C)).X n := sorry

/-- The total degree of a fourfold homogeneous tensor after multiplying the two middle
`B`-factors. -/
theorem contractionDegree (i j k l p q n : ℤ)
    (hij : i + j = p) (hkl : k + l = q) (hpq : p + q = n) :
    i + ((j + k) + l) = n := sorry

/-- Middle multiplication on one fourfold homogeneous tensor summand. -/
noncomputable def contractionSummand (A B C : CochainDGAlgebra.{u, v} R)
    (n p q i j k l : ℤ) (hij : i + j = p) (hkl : k + l = q)
    (hpq : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R)
        (CochainDGAlgebra.Tensor.baseTensor (R := R) (A.opposite.X i) (B.X j))
        (CochainDGAlgebra.Tensor.baseTensor (R := R) (B.opposite.X k) (C.X l)) ⟶
      (CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C)).X n :=
  ModuleCat.ofHom
      (_root_.TensorProduct.tensorTensorTensorAssoc R
        (A.opposite.X i) (B.X j) (B.opposite.X k) (C.X l)).toLinearMap ≫
    ModuleCat.TensorProduct.map R
        (ModuleCat.TensorProduct.map R (𝟙 (A.opposite.X i))
          (CochainDGAlgebra.Tensor.multiplicationComponent B j k (j + k)
            (CochainDGAlgebra.Tensor.totalDegree j k)))
        (𝟙 (C.X l)) ≫
    ModuleCat.ofHom
      (_root_.TensorProduct.assoc R (A.opposite.X i) (B.X (j + k)) (C.X l)).toLinearMap ≫
    ModuleCat.TensorProduct.map R (𝟙 (A.opposite.X i))
      (CochainDGAlgebra.Tensor.summandInclusion B C (j + k) l ((j + k) + l)
        (CochainDGAlgebra.Tensor.totalDegree (j + k) l)) ≫
    CochainDGAlgebra.Tensor.summandInclusion A.opposite
      (CochainDGAlgebra.tensorProduct B C) i ((j + k) + l) n
        (contractionDegree i j k l p q n hij hkl hpq)

/-- On a fourfold pure tensor, `contractionSummand` multiplies the two middle `B`-factors and
retains the two outer factors. -/
theorem contractionSummand_tmul (A B C : CochainDGAlgebra.{u, v} R)
    (n p q i j k l : ℤ) (hij : i + j = p) (hkl : k + l = q)
    (hpq : p + q = n) (a : A.opposite.X i) (b : B.X j)
    (b' : B.opposite.X k) (c : C.X l) :
    (contractionSummand A B C n p q i j k l hij hkl hpq).hom
        ((a ⊗ₜ[R] b) ⊗ₜ[R] (b' ⊗ₜ[R] c)) =
      (CochainDGAlgebra.Tensor.summandInclusion A.opposite
        (CochainDGAlgebra.tensorProduct B C) i ((j + k) + l) n
          (contractionDegree i j k l p q n hij hkl hpq)).hom
        (a ⊗ₜ[R]
          (CochainDGAlgebra.Tensor.summandInclusion B C
            (j + k) l ((j + k) + l)
              (CochainDGAlgebra.Tensor.totalDegree (j + k) l)).hom
            (B.mul j k b b' ⊗ₜ[R] c)) := sorry

/-- Fixing the left homogeneous tensor turns middle multiplication into a map out of one
homogeneous summand of `B.opposite ⊗[R] C`. -/
noncomputable def contractionRightComponent (A B C : CochainDGAlgebra.{u, v} R)
    (n p q i j : ℤ) (hij : i + j = p) (hpq : p + q = n)
    (x : CochainDGAlgebra.Tensor.baseTensor (R := R) (A.opposite.X i) (B.X j))
    (k l : ℤ) (hkl : k + l = q) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (B.opposite.X k) (C.X l) ⟶
      (CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C)).X n :=
  ModuleCat.ofHom
    { toFun := fun y ↦
        (contractionSummand A B C n p q i j k l hij hkl hpq).hom (x ⊗ₜ[R] y)
      map_add' := sorry
      map_smul' := sorry }

/-- Fixing the left homogeneous tensor extends middle multiplication across the right inner
total tensor complex. -/
noncomputable def contractionRightDesc (A B C : CochainDGAlgebra.{u, v} R)
    (n p q i j : ℤ) (hij : i + j = p) (hpq : p + q = n)
    (x : CochainDGAlgebra.Tensor.baseTensor (R := R) (A.opposite.X i) (B.X j)) :
    (CochainDGAlgebra.Tensor.complex B.opposite C).X q ⟶
      (CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C)).X n :=
  mapBifunctorDesc (K₁ := B.opposite.toCochainComplex) (K₂ := C.toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (c := up ℤ)
    (fun k l hkl ↦ contractionRightComponent A B C n p q i j hij hpq x k l hkl)

/-- Fixing an element of the right inner total complex gives the contraction on one left
homogeneous tensor summand. -/
noncomputable def contractionLeftComponent (A B C : CochainDGAlgebra.{u, v} R)
    (n p q : ℤ) (hpq : p + q = n)
    (y : (CochainDGAlgebra.Tensor.complex B.opposite C).X q)
    (i j : ℤ) (hij : i + j = p) :
    CochainDGAlgebra.Tensor.baseTensor (R := R) (A.opposite.X i) (B.X j) ⟶
      (CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C)).X n :=
  ModuleCat.ofHom
    { toFun := fun x ↦ (contractionRightDesc A B C n p q i j hij hpq x).hom y
      map_add' := sorry
      map_smul' := sorry }

/-- Fixing an element of the right inner total complex extends middle multiplication across the
left inner total tensor complex. -/
noncomputable def contractionLeftDesc (A B C : CochainDGAlgebra.{u, v} R)
    (n p q : ℤ) (hpq : p + q = n)
    (y : (CochainDGAlgebra.Tensor.complex B.opposite C).X q) :
    (CochainDGAlgebra.Tensor.complex A.opposite B).X p ⟶
      (CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C)).X n :=
  mapBifunctorDesc (K₁ := A.opposite.toCochainComplex) (K₂ := B.toCochainComplex)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (c := up ℤ)
    (fun i j hij ↦ contractionLeftComponent A B C n p q hpq y i j hij)

/-- The degree-`n` contraction on one outer homogeneous tensor summand. -/
noncomputable def contractionComponent (A B C : CochainDGAlgebra.{u, v} R)
    (n p q : ℤ) (hpq : p + q = n) :
    CochainDGAlgebra.Tensor.baseTensor (R := R)
        ((CochainDGAlgebra.Tensor.complex A.opposite B).X p)
        ((CochainDGAlgebra.Tensor.complex B.opposite C).X q) ⟶
      (CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C)).X n :=
  ModuleCat.TensorProduct.liftOfBilinear R
    (fun x y ↦ (contractionLeftDesc A B C n p q hpq y).hom x)
    sorry sorry sorry sorry

/-- Contract the two middle `B`-factors in the ground-ring tensor complex
`(A ⊗[R] B) ⊗[R] (B ⊗[R] C)`, using tensor associativity and DGA multiplication. -/
@[stacks 0BZ4 "contraction of the middle algebra factors"]
noncomputable def groundContraction (A B C : CochainDGAlgebra.{u, v} R) :
    CochainDGAlgebra.Tensor.complex
        (CochainDGAlgebra.tensorProduct A.opposite B)
        (CochainDGAlgebra.tensorProduct B.opposite C) ⟶
      CochainDGAlgebra.Tensor.complex A.opposite
        (CochainDGAlgebra.tensorProduct B C) where
  f n := mapBifunctorDesc
    (K₁ := CochainDGAlgebra.Tensor.complex A.opposite B)
    (K₂ := CochainDGAlgebra.Tensor.complex B.opposite C)
    (F := CochainDGAlgebra.Tensor.baseBifunctor (R := R)) (c := up ℤ)
    (fun p q hpq ↦ contractionComponent A B C n p q hpq)
  comm' := sorry

/-- On a fourfold homogeneous tensor summand, `groundContraction` is middle multiplication
followed by the canonical inclusions into the right-associated total tensor complex. -/
@[reassoc]
theorem ι_groundContraction (A B C : CochainDGAlgebra.{u, v} R)
    (n p q i j k l : ℤ) (hij : i + j = p) (hkl : k + l = q)
    (hpq : p + q = n) :
    ModuleCat.TensorProduct.map R
        (CochainDGAlgebra.Tensor.summandInclusion A.opposite B i j p hij)
        (CochainDGAlgebra.Tensor.summandInclusion B.opposite C k l q hkl) ≫
      CochainDGAlgebra.Tensor.summandInclusion
        (CochainDGAlgebra.tensorProduct A.opposite B)
        (CochainDGAlgebra.tensorProduct B.opposite C) p q n hpq ≫
      (groundContraction A B C).f n =
        contractionSummand A B C n p q i j k l hij hkl hpq := sorry

/-- The tensor totalization of the two algebra-tensor bimodules has the literal source complex
`(A ⊗[R] B) ⊗[R] (B ⊗[R] C)` for middle-factor contraction. -/
@[stacks 0BZ4 "source complex of the algebra contraction"]
theorem contractionSourceComplex (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.TensorProduct.rawComplex
        (algebra A B).toRightModule (algebra B C).toLeftModule =
      CochainDGAlgebra.Tensor.complex
        (CochainDGAlgebra.tensorProduct A.opposite B)
        (CochainDGAlgebra.tensorProduct B.opposite C) := sorry

/-- The ground contraction transported to the underlying complexes of the relative-tensor
factors and the literal triple-tensor target. -/
@[stacks 0BZ4 "raw algebra contraction"]
noncomputable def rawContraction (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.TensorProduct.rawComplex
        (algebra A B).toRightModule (algebra B C).toLeftModule ⟶
      (tripleRightModule A B C).toCochainComplex :=
  eqToHom (contractionSourceComplex A B C) ≫
    groundContraction A B C ≫
    eqToHom (tripleRightModule_toCochainComplex A B C).symm

/-- The homogeneous pairing underlying the middle-factor contraction. -/
@[stacks 0BZ4 "homogeneous pairing for algebra contraction"]
noncomputable def pairing (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.TensorProduct.Pairing
      (algebra A B).toRightModule
      (algebra B C).toLeftModule
      (tripleRightModule A B C).toCochainComplex :=
  fun p q ↦
      ιMapBifunctor
        (DifferentialGradedModule.TensorProduct.rightComplex
          (algebra A B).toRightModule)
        (DifferentialGradedModule.TensorProduct.leftComplex
          (algebra B C).toLeftModule)
        (DifferentialGradedModule.TensorProduct.baseBifunctor (R := R))
        (up ℤ) p q (p + q) rfl ≫
      (rawContraction A B C).f (p + q)

/-- The middle-factor contraction is balanced over `B`, hence factors through the ordinary
relative tensor product. -/
@[stacks 0BZ4 "balanced algebra contraction pairing"]
theorem pairing_isBalanced (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.TensorProduct.IsBalanced
      (algebra A B).toRightModule
      (algebra B C).toLeftModule
      (pairing A B C) := sorry

/-- The balanced middle-factor contraction commutes with the total differentials. -/
@[stacks 0BZ4 "differential compatibility of algebra contraction"]
theorem pairing_isDifferentialCompatible (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.TensorProduct.IsDifferentialCompatible
      (algebra A B).toRightModule
      (algebra B C).toLeftModule
      (pairing A B C) := sorry

/-- The cochain map from the ordinary relative tensor to the literal triple ground tensor,
obtained by descending the balanced middle-factor contraction. -/
@[stacks 0BZ4 "cochain-level algebra contraction"]
noncomputable def contractionCochainMap (A B C : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.TensorProduct.complex
        (algebra A B).toRightModule
        (algebra B C).toLeftModule ⟶
      (tripleRightModule A B C).toCochainComplex :=
  DifferentialGradedModule.TensorProduct.lift
    (algebra A B).toRightModule
    (algebra B C).toLeftModule
    (pairing A B C) (pairing_isBalanced A B C)
    (pairing_isDifferentialCompatible A B C)

/-- The canonical right `C`-linear contraction
`(A ⊗[R] B) ⊗_B (B ⊗[R] C) ⟶ A ⊗[R] (B ⊗[R] C)`. -/
@[stacks 0BZ4 "ordinary relative tensor to the algebra triple tensor"]
noncomputable def contraction (A B C : CochainDGAlgebra.{u, v} R) :
    relativeModule A B C ⟶ tripleRightModule A B C where
  hom n := ((contractionCochainMap A B C).f n).hom
  comm_d := sorry
  comm_smul := sorry

/-- Contracting the two middle `B`-factors identifies the ordinary relative tensor with the
literal ground-ring triple tensor. -/
@[stacks 0BZ4 "isomorphism of ordinary and triple tensor modules"]
noncomputable instance contraction_isIso (A B C : CochainDGAlgebra.{u, v} R) :
    IsIso (contraction A B C) := sorry

/-- The canonical differential graded `(A, C)`-bimodule contraction
`(A ⊗[R] B) ⊗_B (B ⊗[R] C) ⟶ A ⊗[R] (B ⊗[R] C)`. -/
@[stacks 0BZ4 "ordinary relative tensor bimodule to the algebra triple tensor"]
noncomputable def bimoduleContraction (A B C : CochainDGAlgebra.{u, v} R) :
    bimodule (algebra A B) (algebra B C) ⟶ tripleBimodule A B C where
  hom := (contraction A B C).hom
  comm_d := sorry
  comm_smul := sorry

/-- The bimodule contraction is an isomorphism: relative tensoring contracts the two adjacent
copies of the middle algebra. -/
@[stacks 0BZ4 "isomorphism of algebra triple bimodules"]
noncomputable instance bimoduleContraction_isIso
    (A B C : CochainDGAlgebra.{u, v} R) :
    IsIso (bimoduleContraction A B C) := sorry

/-- The middle-factor contraction as a morphism in the differential graded homotopy category. -/
@[stacks 0BZ4 "homotopy-category algebra contraction"]
noncomputable def contractionOnK (A B C : CochainDGAlgebra.{u, v} R) :
    (⟨relativeModule A B C⟩ : K R (DifferentialGradedModule.{u, v} C)) ⟶
      ⟨tripleRightModule A B C⟩ :=
  (DifferentialGradedModule.homToCompHom (contraction A B C)).toHomotopyClass

end DifferentialGradedBimodule.Tensor.AlgebraTensor
