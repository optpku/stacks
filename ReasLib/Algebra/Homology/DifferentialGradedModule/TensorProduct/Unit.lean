module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct

/-!
# The Regular Module as a Tensor Unit

This file constructs the canonical isomorphism `A ⊗_A N ≅ N` for a left differential graded
`A`-module.  Both directions are explicit: multiplication evaluates a balanced tensor, while
the inverse sends `x` to `1 ⊗ x`.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open ComplexShape
open HomologicalComplex

namespace DifferentialGradedModule.TensorProduct

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- Evaluate two homogeneous inputs by the left module action and transport to the specified
total degree. -/
def regularEvaluationValue (N : LeftDifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) (a : A.X p) (x : N.X q) : N.X n :=
  cast (congrArg (fun i : ℤ ↦ (N.X i : Type v)) h) (N.smul p q a x)

/-- Regular evaluation is additive in its algebra input. -/
theorem regularEvaluationValue_add_left (N : LeftDifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) (a b : A.X p) (x : N.X q) :
    regularEvaluationValue N n p q h (a + b) x =
      regularEvaluationValue N n p q h a x + regularEvaluationValue N n p q h b x := sorry

/-- Regular evaluation is `R`-linear in its algebra input. -/
theorem regularEvaluationValue_smul_left (N : LeftDifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) (r : R) (a : A.X p) (x : N.X q) :
    regularEvaluationValue N n p q h (r • a) x =
      r • regularEvaluationValue N n p q h a x := sorry

/-- Regular evaluation is additive in its module input. -/
theorem regularEvaluationValue_add_right (N : LeftDifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) (a : A.X p) (x y : N.X q) :
    regularEvaluationValue N n p q h a (x + y) =
      regularEvaluationValue N n p q h a x + regularEvaluationValue N n p q h a y := sorry

/-- Regular evaluation is `R`-linear in its module input. -/
theorem regularEvaluationValue_smul_right (N : LeftDifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) (r : R) (a : A.X p) (x : N.X q) :
    regularEvaluationValue N n p q h a (r • x) =
      r • regularEvaluationValue N n p q h a x := sorry

/-- Evaluation of one homogeneous tensor summand by the left module action. -/
def regularEvaluationComponent (N : LeftDifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) :
    baseTensor (R := R) (A.regularModule.X p) (N.X q) ⟶ N.X n :=
  ModuleCat.TensorProduct.lift R <| LinearMap.mk₂ R
    (regularEvaluationValue N n p q h)
    (regularEvaluationValue_add_left N n p q h)
    (regularEvaluationValue_smul_left N n p q h)
    (regularEvaluationValue_add_right N n p q h)
    (regularEvaluationValue_smul_right N n p q h)

/-- Evaluation on the unbalanced total tensor term. -/
def regularEvaluationDesc (N : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    rawTerm A.regularModule N n ⟶ N.X n :=
  mapBifunctorDesc (K₁ := rightComplex A.regularModule) (K₂ := leftComplex N)
    (F := baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ regularEvaluationComponent N n p q h)

/-- The linear evaluation map before passing to the balancing quotient. -/
def regularEvaluationRaw (N : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    rawTerm A.regularModule N n →ₗ[R] N.X n :=
  (regularEvaluationDesc N n).hom

/-- Evaluation kills the homogeneous balancing relations. -/
theorem regularEvaluation_relations (N : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    relations A.regularModule N n ≤ LinearMap.ker (regularEvaluationRaw N n) := sorry

/-- Evaluation descended to the relative tensor quotient in one degree. -/
def regularEvaluationLinear (N : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    family A.regularModule N n →ₗ[R] N.X n :=
  (relations A.regularModule N n).liftQ
    (regularEvaluationRaw N n) (regularEvaluation_relations N n)

/-- Degreewise regular evaluation commutes with the cochain differentials. -/
theorem regularEvaluation_comm (N : LeftDifferentialGradedModule.{u, v} A)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ModuleCat.ofHom (regularEvaluationLinear N i) ≫ N.toCochainComplex.d i j =
      (complex A.regularModule N).d i j ≫
        ModuleCat.ofHom (regularEvaluationLinear N j) := sorry

/-- The cochain map `A ⊗_A N ⟶ N` induced by the left `A`-action. -/
def regularEvaluation (N : LeftDifferentialGradedModule.{u, v} A) :
    complex A.regularModule N ⟶ N.toCochainComplex where
  f n := ModuleCat.ofHom (regularEvaluationLinear N n)
  comm' := regularEvaluation_comm N

/-- The value of coevaluation is the pure tensor `1 ⊗ x`, reindexed from degree `0 + n`. -/
def regularCoevaluationValue (N : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : N.X n) : family A.regularModule N n :=
  cast (congrArg (fun i : ℤ ↦ (family A.regularModule N i : Type v)) (zero_add n))
    (tmul A.regularModule N A.one x)

/-- Regular coevaluation preserves addition. -/
theorem regularCoevaluationValue_add (N : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x y : N.X n) :
    regularCoevaluationValue N n (x + y) =
      regularCoevaluationValue N n x + regularCoevaluationValue N n y := sorry

/-- Regular coevaluation preserves `R`-scalar multiplication. -/
theorem regularCoevaluationValue_smul (N : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (r : R) (x : N.X n) :
    regularCoevaluationValue N n (r • x) = r • regularCoevaluationValue N n x := sorry

/-- Insert the unit as the degree-zero first tensor factor. -/
def regularCoevaluationLinear (N : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    N.X n →ₗ[R] family A.regularModule N n where
  toFun := regularCoevaluationValue N n
  map_add' := regularCoevaluationValue_add N n
  map_smul' := regularCoevaluationValue_smul N n

/-- Degreewise regular coevaluation commutes with the cochain differentials. -/
theorem regularCoevaluation_comm (N : LeftDifferentialGradedModule.{u, v} A)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ModuleCat.ofHom (regularCoevaluationLinear N i) ≫
        (complex A.regularModule N).d i j =
      N.toCochainComplex.d i j ≫ ModuleCat.ofHom (regularCoevaluationLinear N j) := sorry

/-- The cochain map `N ⟶ A ⊗_A N` sending `x` to `1 ⊗ x`. -/
def regularCoevaluation (N : LeftDifferentialGradedModule.{u, v} A) :
    N.toCochainComplex ⟶ complex A.regularModule N where
  f n := ModuleCat.ofHom (regularCoevaluationLinear N n)
  comm' := regularCoevaluation_comm N

/-- Evaluation followed by coevaluation is the identity of the relative tensor complex. -/
theorem regularEvaluation_comp_coevaluation (N : LeftDifferentialGradedModule.{u, v} A) :
    regularEvaluation N ≫ regularCoevaluation N = 𝟙 (complex A.regularModule N) := sorry

/-- Coevaluation followed by evaluation is the identity of the left module complex. -/
theorem regularCoevaluation_comp_evaluation (N : LeftDifferentialGradedModule.{u, v} A) :
    regularCoevaluation N ≫ regularEvaluation N = 𝟙 N.toCochainComplex := sorry

/-- Section 22.12 (09LL): the regular right DG module is the left unit for relative tensor
product. -/
@[stacks 09LL "regular differential graded module is a relative tensor unit"]
def regularTensorIso (N : LeftDifferentialGradedModule.{u, v} A) :
    complex A.regularModule N ≅ N.toCochainComplex where
  hom := regularEvaluation N
  inv := regularCoevaluation N
  hom_inv_id := regularEvaluation_comp_coevaluation N
  inv_hom_id := regularCoevaluation_comp_evaluation N

/-- The tensor-unit isomorphism evaluates a homogeneous pure tensor by the left action. -/
theorem regularTensorIso_hom_tmul (N : LeftDifferentialGradedModule.{u, v} A)
    (p q : ℤ) (a : A.X p) (x : N.X q) :
    ModuleCat.Hom.hom ((regularTensorIso N).hom.f (p + q))
        (tmul A.regularModule N a x) =
      N.smul p q a x := sorry

/-- The inverse tensor-unit isomorphism sends an element to the pure tensor `1 ⊗ x`. -/
theorem regularTensorIso_inv_apply (N : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : N.X n) :
    ModuleCat.Hom.hom ((regularTensorIso N).inv.f n) x =
      regularCoevaluationValue N n x := sorry

/-- Evaluate a homogeneous element of a right module against a homogeneous algebra element. -/
def rightRegularEvaluationValue (M : DifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) (x : M.X p) (a : A.X q) : M.X n :=
  cast (congrArg (fun i : ℤ ↦ (M.X i : Type v)) h) (M.smul p q x a)

/-- Evaluation against the regular left module is bilinear. -/
def rightRegularEvaluationComponent (M : DifferentialGradedModule.{u, v} A)
    (n p q : ℤ) (h : p + q = n) :
    baseTensor (R := R) (M.X p) (A.leftRegularModule.X q) ⟶ M.X n :=
  ModuleCat.TensorProduct.lift R <| LinearMap.mk₂ R
    (rightRegularEvaluationValue M n p q h) sorry sorry sorry sorry

/-- Evaluation on the raw total tensor with the regular left module. -/
def rightRegularEvaluationDesc (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    rawTerm M A.leftRegularModule n ⟶ M.X n :=
  mapBifunctorDesc (K₁ := rightComplex M) (K₂ := leftComplex A.leftRegularModule)
    (F := baseBifunctor (R := R)) (c := up ℤ)
    (fun p q h ↦ rightRegularEvaluationComponent M n p q h)

/-- The raw evaluation map for tensoring with the regular left module. -/
def rightRegularEvaluationRaw (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    rawTerm M A.leftRegularModule n →ₗ[R] M.X n :=
  (rightRegularEvaluationDesc M n).hom

/-- Right-module evaluation kills the homogeneous balancing relations. -/
theorem rightRegularEvaluation_relations (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    relations M A.leftRegularModule n ≤
      LinearMap.ker (rightRegularEvaluationRaw M n) := sorry

/-- Evaluation descended to `M ⊗_A A` in one degree. -/
def rightRegularEvaluationLinear (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    family M A.leftRegularModule n →ₗ[R] M.X n :=
  (relations M A.leftRegularModule n).liftQ
    (rightRegularEvaluationRaw M n) (rightRegularEvaluation_relations M n)

/-- The descended right-unit evaluation commutes with differentials. -/
theorem rightRegularEvaluation_comm (M : DifferentialGradedModule.{u, v} A)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ModuleCat.ofHom (rightRegularEvaluationLinear M i) ≫ M.toCochainComplex.d i j =
      (complex M A.leftRegularModule).d i j ≫
        ModuleCat.ofHom (rightRegularEvaluationLinear M j) := sorry

/-- The canonical cochain map `M ⊗_ A ⟶ M` induced by the right `A`-action. -/
def rightRegularEvaluation (M : DifferentialGradedModule.{u, v} A) :
    complex M A.leftRegularModule ⟶ M.toCochainComplex where
  f n := ModuleCat.ofHom (rightRegularEvaluationLinear M n)
  comm' := rightRegularEvaluation_comm M

/-- Insert the unit as the degree-zero second tensor factor. -/
def rightRegularCoevaluationValue (M : DifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : M.X n) : family M A.leftRegularModule n :=
  cast (congrArg (fun i : ℤ ↦ (family M A.leftRegularModule i : Type v)) (add_zero n))
    (tmul M A.leftRegularModule x A.one)

/-- Insertion of the unit as the second factor is linear in each degree. -/
def rightRegularCoevaluationLinear (M : DifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.X n →ₗ[R] family M A.leftRegularModule n where
  toFun := rightRegularCoevaluationValue M n
  map_add' := sorry
  map_smul' := sorry

/-- Right-unit coevaluation commutes with differentials. -/
theorem rightRegularCoevaluation_comm (M : DifferentialGradedModule.{u, v} A)
    (i j : ℤ) (hij : (up ℤ).Rel i j) :
    ModuleCat.ofHom (rightRegularCoevaluationLinear M i) ≫
        (complex M A.leftRegularModule).d i j =
      M.toCochainComplex.d i j ≫ ModuleCat.ofHom (rightRegularCoevaluationLinear M j) := sorry

/-- The cochain map `M ⟶ M ⊗_A A` which inserts the unit in the second factor. -/
def rightRegularCoevaluation (M : DifferentialGradedModule.{u, v} A) :
    M.toCochainComplex ⟶ complex M A.leftRegularModule where
  f n := ModuleCat.ofHom (rightRegularCoevaluationLinear M n)
  comm' := rightRegularCoevaluation_comm M

/-- Right-unit evaluation followed by coevaluation is the identity. -/
theorem rightRegularEvaluation_comp_coevaluation (M : DifferentialGradedModule.{u, v} A) :
    rightRegularEvaluation M ≫ rightRegularCoevaluation M =
      𝟙 (complex M A.leftRegularModule) := sorry

/-- Right-unit coevaluation followed by evaluation is the identity. -/
theorem rightRegularCoevaluation_comp_evaluation (M : DifferentialGradedModule.{u, v} A) :
    rightRegularCoevaluation M ≫ rightRegularEvaluation M = 𝟙 M.toCochainComplex := sorry

/-- The regular left DG module is the right unit for relative tensor product. -/
@[stacks 09LL "regular differential graded module is a relative tensor right unit"]
def rightRegularTensorIso (M : DifferentialGradedModule.{u, v} A) :
    complex M A.leftRegularModule ≅ M.toCochainComplex where
  hom := rightRegularEvaluation M
  inv := rightRegularCoevaluation M
  hom_inv_id := rightRegularEvaluation_comp_coevaluation M
  inv_hom_id := rightRegularCoevaluation_comp_evaluation M

/-- The right-unit isomorphism evaluates a pure tensor by the right module action. -/
theorem rightRegularTensorIso_hom_tmul (M : DifferentialGradedModule.{u, v} A)
    (p q : ℤ) (x : M.X p) (a : A.X q) :
    ModuleCat.Hom.hom ((rightRegularTensorIso M).hom.f (p + q))
        (tmul M A.leftRegularModule x a) = M.smul p q x a := sorry

end DifferentialGradedModule.TensorProduct
