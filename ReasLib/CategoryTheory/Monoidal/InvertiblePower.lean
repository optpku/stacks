/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.CategoryTheory.Equivalence.Power

/-!
# Integral powers of tensor autoequivalences

This file owns the category-theoretic operation underlying integral tensor powers: the integer
power of tensoring on the right by an invertible object, evaluated at an arbitrary base object.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe v u

namespace CategoryTheory.MonoidalCategory.InvertiblePower

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- Evaluate the `n`th power of the tensor-right autoequivalence associated to `L` at a base
object `A`. -/
@[stacks 01CU "categorical integral tensor-power owner"]
noncomputable abbrev eval
    (L A : C) [isInvertibleObject L] (n : ℤ) : C :=
  ((tensorRight L).asEquivalence ^ n).functor.obj A

/-- The autoequivalence expression defining `InvertiblePower.eval`. -/
theorem eval_def
    (L A : C) [isInvertibleObject L] (n : ℤ) :
    eval L A n = ((tensorRight L).asEquivalence ^ n).functor.obj A := rfl

/-- The integral tensor power of an invertible object, based at the monoidal unit. -/
noncomputable abbrev obj
    (L : C) [isInvertibleObject L] (n : ℤ) : C :=
  eval L (𝟙_ C) n

/-- `InvertiblePower.obj` is `InvertiblePower.eval` evaluated at the monoidal unit. -/
theorem obj_def
    (L : C) [isInvertibleObject L] (n : ℤ) :
    obj L n = eval L (𝟙_ C) n := rfl

/-- Transport an integral tensor orbit along an equality of its degrees. -/
noncomputable def evalIndexIso
    (L A : C) [isInvertibleObject L] {m n : ℤ} (h : m = n) :
    eval L A m ≅ eval L A n :=
  Equivalence.powObjIndexIso (tensorRight L).asEquivalence A h

/-- The integral tensor action preserves isomorphisms between base objects. -/
noncomputable def evalMapIso
    (L : C) [isInvertibleObject L] {A B : C} (e : A ≅ B) (n : ℤ) :
    eval L A n ≅ eval L B n :=
  Equivalence.powObjMapIso (tensorRight L).asEquivalence e n

/-- Transport categorical integral tensor powers along an equality of their degrees. -/
noncomputable def indexIso
    (L : C) [isInvertibleObject L] {m n : ℤ} (h : m = n) :
    obj L m ≅ obj L n :=
  evalIndexIso L (𝟙_ C) h

/-- The zeroth integral tensor action fixes every base object. -/
@[stacks 01CU "zeroth integral tensor action"]
noncomputable def evalZeroIso
    (L A : C) [isInvertibleObject L] : eval L A 0 ≅ A :=
  (Equivalence.powZeroIso (tensorRight L).asEquivalence).app A

/-- Applying the integral tensor action and then tensoring on the right by `L` raises the degree
by one. This is the reusable functor-orbit comparison underlying integral tensor powers. -/
@[stacks 01CU "right successor for the integral tensor action"]
noncomputable def evalRightSuccIso
    (L A : C) [isInvertibleObject L] (n : ℤ) :
    eval L A n ⊗ L ≅ eval L A (n + 1) :=
  (Equivalence.powRightSuccIso (tensorRight L).asEquivalence n).app A

/-- In a braided category, applying the integral tensor action and then tensoring on the left by
`L` raises the degree by one. -/
@[stacks 01CU "left successor for the integral tensor action"]
noncomputable def evalOneAddIso [BraidedCategory C]
    (L A : C) [isInvertibleObject L] (n : ℤ) :
    L ⊗ eval L A n ≅ eval L A (n + 1) :=
  β_ L (eval L A n) ≪≫ evalRightSuccIso L A n

/-- A tensor orbit step of degree `m + n` is canonically the composite of the degree-`m` and
degree-`n` steps. -/
@[stacks 01CU "addition for the integral tensor action"]
noncomputable def evalAddIso
    (L A : C) [isInvertibleObject L] (m n : ℤ) :
    eval L A (m + n) ≅ eval L (eval L A m) n :=
  Equivalence.powObjAddIso (tensorRight L).asEquivalence A m n

/-- Associativity of successive integral tensor-action steps. -/
theorem evalAddIso_assoc_hom
    (L A : C) [isInvertibleObject L] (m n k : ℤ) :
    (evalAddIso L A (m + n) k).hom ≫
        ((tensorRight L).asEquivalence ^ k).functor.map
          (evalAddIso L A m n).hom =
      (evalIndexIso L A (Int.add_assoc m n k)).hom ≫
        (evalAddIso L A m (n + k)).hom ≫
        (evalAddIso L (eval L A m) n k).hom := by
  dsimp [eval, evalAddIso, evalIndexIso, Equivalence.powObjAddIso,
    Equivalence.powObjIndexIso, Equivalence.powIndexIso, Functor.comp]
  simpa only [Iso.app_hom, eqToIso.hom, eqToHom_app, Functor.comp] using
    Equivalence.powAddIso_assoc_hom_app
      (tensorRight L).asEquivalence m n k A

/-- Left-unit law for the addition comparison of the integral tensor action. -/
theorem evalAddIso_zero_add_hom
    (L A : C) [isInvertibleObject L] (n : ℤ) :
    (evalAddIso L A 0 n).hom =
      (evalIndexIso L A (Int.zero_add n)).hom ≫
        ((tensorRight L).asEquivalence ^ n).functor.map (evalZeroIso L A).inv := by
  dsimp [eval, evalAddIso, evalIndexIso, evalZeroIso,
    Equivalence.powObjAddIso, Equivalence.powObjIndexIso,
    Equivalence.powIndexIso, Functor.comp, Functor.id, Equivalence.refl]
  simpa only [Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToHom_app,
    Functor.comp, Functor.id, Equivalence.refl, Equivalence.pow_zero] using
    Equivalence.powAddIso_zero_add_hom_app
      (tensorRight L).asEquivalence n A

/-- Right-unit law for the addition comparison of the integral tensor action. -/
theorem evalAddIso_add_zero_hom
    (L A : C) [isInvertibleObject L] (n : ℤ) :
    (evalAddIso L A n 0).hom =
      (evalIndexIso L A (Int.add_zero n)).hom ≫
        (evalZeroIso L (eval L A n)).inv := by
  dsimp [eval, evalAddIso, evalIndexIso, evalZeroIso,
    Equivalence.powObjAddIso, Equivalence.powObjIndexIso,
    Equivalence.powIndexIso, Functor.comp, Functor.id, Equivalence.refl]
  simpa only [Iso.app_hom, Iso.app_inv, eqToIso.hom, eqToHom_app,
    Functor.comp, Functor.id, Equivalence.refl, Equivalence.pow_zero] using
    Equivalence.powAddIso_add_zero_hom_app
      (tensorRight L).asEquivalence n A

/-- The zeroth integral tensor power is canonically the monoidal unit. -/
@[stacks 01CU "zeroth categorical integral tensor power"]
noncomputable def zeroIso
    (L : C) [isInvertibleObject L] : obj L 0 ≅ 𝟙_ C :=
  Iso.refl _

/-- Tensoring an integral tensor power on the right by `L` raises its degree by one. -/
@[stacks 01CU "right successor for categorical integral tensor powers"]
noncomputable def rightSuccIso
    (L : C) [isInvertibleObject L] (n : ℤ) :
    obj L n ⊗ L ≅ obj L (n + 1) :=
  evalRightSuccIso L (𝟙_ C) n

namespace Aux

/-- Adding negative one on the left is subtraction by one. -/
theorem negOneAdd (n : ℤ) : (-1 : ℤ) + n = n - 1 := by omega

/-- The next negative successor is obtained by adding negative one on the left. -/
theorem negSuccEq (n : ℕ) :
    Int.negSucc (n + 1) = (-1 : ℤ) + Int.negSucc n := by omega

/-- Positive one and negative one add to zero. -/
theorem oneAddNegOne : (1 : ℤ) + (-1 : ℤ) = 0 := by omega

end Aux

/-- The inverse of tensoring on the right is naturally tensoring on the right with its value at
the monoidal unit. This is the functor-level negative-degree base case. -/
@[stacks 01CU "inverse tensor action functor comparison"]
noncomputable def evalNegOneFunctorIso
    (L : C) [isInvertibleObject L] :
    (tensorRight L).asEquivalence.inverse ≅ tensorRight (obj L (-1)) :=
  let e := (tensorRight L).asEquivalence
  let j : 𝟭 C ≅ tensorRight (e.inverse.obj (𝟙_ C)) ⋙ e.functor :=
    (rightUnitorNatIso C).symm ≪≫
      (tensoringRight C).mapIso (e.counitIso.app (𝟙_ C)).symm ≪≫
      tensorRightTensor (e.inverse.obj (𝟙_ C)) L
  (Functor.leftUnitor e.inverse).symm ≪≫
    Functor.isoWhiskerRight j e.inverse ≪≫
    Functor.associator (tensorRight (e.inverse.obj (𝟙_ C))) e.functor e.inverse ≪≫
    Functor.isoWhiskerLeft (tensorRight (e.inverse.obj (𝟙_ C))) e.unitIso.symm ≪≫
    Functor.rightUnitor (tensorRight (e.inverse.obj (𝟙_ C)))

/-- The inverse of tensoring on the right acts by tensoring on the right with its value at the
monoidal unit. This is the objectwise negative-degree base case. -/
@[stacks 01CU "inverse tensor action"]
noncomputable def evalNegOneIso
    (L A : C) [isInvertibleObject L] :
    eval L A (-1) ≅ A ⊗ obj L (-1) :=
  (evalNegOneFunctorIso L).app A

/-- A component of the functor-level inverse tensor action is its objectwise comparison. -/
@[simp, stacks 01CU "inverse tensor action functor component"]
theorem evalNegOneFunctorIso_app
    (L A : C) [isInvertibleObject L] :
    (evalNegOneFunctorIso L).app A = evalNegOneIso L A := rfl

/-- The degree-minus-one tensor-orbit comparison is natural in the base object. -/
@[reassoc, stacks 01CU "degree-minus-one tensor-orbit naturality"]
theorem evalNegOneIso_naturality
    (L : C) [isInvertibleObject L] {A B : C} (f : A ⟶ B) :
    (tensorRight L).asEquivalence.inverse.map f ≫ (evalNegOneIso L B).hom =
      (evalNegOneIso L A).hom ≫ f ▷ obj L (-1) :=
  (evalNegOneFunctorIso L).hom.naturality f

/-- Tensoring an integral tensor power on the right by the degree `-1` power lowers its degree
by one. -/
@[stacks 01CU "right predecessor for categorical integral tensor powers"]
noncomputable def rightPredIso
    (L : C) [isInvertibleObject L] (n : ℤ) :
    obj L n ⊗ obj L (-1) ≅ obj L (n - 1) :=
  (evalNegOneIso L (obj L n)).symm ≪≫
    (Equivalence.powRightPredIso (tensorRight L).asEquivalence n).app (𝟙_ C)

namespace Aux

/-- The functor-level tensor-orbit comparison in nonnegative degrees. -/
noncomputable def evalTensorOfNatFunctorIso
    (L : C) [isInvertibleObject L] :
    (n : ℕ) →
      ((tensorRight L).asEquivalence ^ (n : ℤ)).functor ≅
        tensorRight (obj L (n : ℤ))
  | 0 =>
      Equivalence.powZeroIso (tensorRight L).asEquivalence ≪≫
        (rightUnitorNatIso C).symm
  | n + 1 =>
      Equivalence.powIndexIso (tensorRight L).asEquivalence
          (Equivalence.PowAux.ofNatSucc n).symm ≪≫
        (Equivalence.powRightSuccIso
          (tensorRight L).asEquivalence (n : ℤ)).symm ≪≫
        Functor.isoWhiskerRight (evalTensorOfNatFunctorIso L n) (tensorRight L) ≪≫
        (tensorRightTensor (obj L (n : ℤ)) L).symm ≪≫
        (tensoringRight C).mapIso (rightSuccIso L (n : ℤ)) ≪≫
        (tensoringRight C).mapIso
          (indexIso L (Equivalence.PowAux.ofNatSucc n))

/-- The tensor-orbit comparison in nonnegative degrees. -/
noncomputable def evalTensorOfNatIso
    (L A : C) [isInvertibleObject L] (n : ℕ) :
    eval L A (n : ℤ) ≅ A ⊗ obj L (n : ℤ) :=
  (evalTensorOfNatFunctorIso L n).app A

/-- The nonnegative tensor-orbit comparisons are natural in the base object. -/
@[reassoc, stacks 01CU "nonnegative tensor-orbit naturality"]
theorem evalTensorOfNatIso_naturality
    (L : C) [isInvertibleObject L] (n : ℕ) {A B : C} (f : A ⟶ B) :
    ((tensorRight L).asEquivalence ^ (n : ℤ)).functor.map f ≫
        (evalTensorOfNatIso L B n).hom =
      (evalTensorOfNatIso L A n).hom ≫
        (tensorRight (obj L (n : ℤ))).map f :=
  (evalTensorOfNatFunctorIso L n).hom.naturality f

/-- The functor-level tensor-orbit comparison in negative degrees. -/
noncomputable def evalTensorNegSuccFunctorIso
    (L : C) [isInvertibleObject L] :
    (n : ℕ) →
      ((tensorRight L).asEquivalence ^ Int.negSucc n).functor ≅
        tensorRight (obj L (Int.negSucc n))
  | 0 => evalNegOneFunctorIso L
  | n + 1 =>
      Equivalence.powIndexIso (tensorRight L).asEquivalence
          (Equivalence.PowAux.negSuccPred n).symm ≪≫
        (Equivalence.powRightPredIso (tensorRight L).asEquivalence
          (Int.negSucc n)).symm ≪≫
        Functor.isoWhiskerLeft
          ((tensorRight L).asEquivalence ^ Int.negSucc n).functor
          (evalNegOneFunctorIso L) ≪≫
        Functor.isoWhiskerRight (evalTensorNegSuccFunctorIso L n)
          (tensorRight (obj L (-1))) ≪≫
        (tensorRightTensor (obj L (Int.negSucc n)) (obj L (-1))).symm ≪≫
        (tensoringRight C).mapIso (rightPredIso L (Int.negSucc n)) ≪≫
        (tensoringRight C).mapIso
          (indexIso L (Equivalence.PowAux.negSuccPred n))

/-- The tensor-orbit comparison in negative degrees. -/
noncomputable def evalTensorNegSuccIso
    (L A : C) [isInvertibleObject L] (n : ℕ) :
    eval L A (Int.negSucc n) ≅ A ⊗ obj L (Int.negSucc n) :=
  (evalTensorNegSuccFunctorIso L n).app A

/-- The negative tensor-orbit comparisons are natural in the base object. -/
@[reassoc, stacks 01CU "negative tensor-orbit naturality"]
theorem evalTensorNegSuccIso_naturality
    (L : C) [isInvertibleObject L] (n : ℕ) {A B : C} (f : A ⟶ B) :
    ((tensorRight L).asEquivalence ^ Int.negSucc n).functor.map f ≫
        (evalTensorNegSuccIso L B n).hom =
      (evalTensorNegSuccIso L A n).hom ≫
        (tensorRight (obj L (Int.negSucc n))).map f :=
  (evalTensorNegSuccFunctorIso L n).hom.naturality f

end Aux

/-- An integral tensor orbit is canonically tensoring on the right by the corresponding power of
the acting object. -/
@[stacks 01CU "tensor model of an integral tensor orbit"]
noncomputable def evalTensorIso
    (L A : C) [isInvertibleObject L] :
    (n : ℤ) → eval L A n ≅ A ⊗ obj L n
  | .ofNat n => Aux.evalTensorOfNatIso L A n
  | .negSucc n => Aux.evalTensorNegSuccIso L A n

/-- The tensor-orbit comparisons are natural in the base object. -/
theorem evalTensorIso_naturality
    (L : C) [isInvertibleObject L] (n : ℤ) {A B : C} (f : A ⟶ B) :
    ((tensorRight L).asEquivalence ^ n).functor.map f ≫
        (evalTensorIso L B n).hom =
      (evalTensorIso L A n).hom ≫ (tensorRight (obj L n)).map f := by
  rcases n with n | n
  · exact Aux.evalTensorOfNatIso_naturality L n f
  · exact Aux.evalTensorNegSuccIso_naturality L n f

/-- The inverse tensor-orbit comparison is natural in the base object. -/
@[stacks 01CU "inverse tensor-orbit comparison naturality"]
theorem evalTensorIso_inv_naturality
    (L : C) [isInvertibleObject L] (n : ℤ) {A B : C} (f : A ⟶ B) :
    (tensorRight (obj L n)).map f ≫
        (evalTensorIso L B n).inv =
      (evalTensorIso L A n).inv ≫
        ((tensorRight L).asEquivalence ^ n).functor.map f := by
  change (f ▷ obj L n) ≫ (evalTensorIso L B n).inv = _
  rw [(evalTensorIso L B n).comp_inv_eq]
  rw [Category.assoc, evalTensorIso_naturality]
  simp

/-- The forward tensor-orbit comparisons form a natural transformation in the base object. -/
@[stacks 01CU "tensor-orbit comparison natural transformation"]
noncomputable def evalFunctorNatTrans
    (L : C) [isInvertibleObject L] (n : ℤ) :
    ((tensorRight L).asEquivalence ^ n).functor ⟶ tensorRight (obj L n) where
  app A := (evalTensorIso L A n).hom
  naturality _ _ f := evalTensorIso_naturality L n f

/-- A component of the forward tensor-orbit natural transformation is the objectwise comparison. -/
@[simp, stacks 01CU "tensor-orbit comparison natural transformation component"]
theorem evalFunctorNatTrans_app
    (L : C) [isInvertibleObject L] (n : ℤ) (A : C) :
    (evalFunctorNatTrans L n).app A = (evalTensorIso L A n).hom := rfl

/-- The inverse tensor-orbit comparisons form a natural transformation in the base object. -/
@[stacks 01CU "inverse tensor-orbit comparison natural transformation"]
noncomputable def evalFunctorNatTransInv
    (L : C) [isInvertibleObject L] (n : ℤ) :
    tensorRight (obj L n) ⟶ ((tensorRight L).asEquivalence ^ n).functor where
  app A := (evalTensorIso L A n).inv
  naturality _ _ f := evalTensorIso_inv_naturality L n f

/-- A component of the inverse tensor-orbit natural transformation is the inverse objectwise
comparison. -/
@[simp, stacks 01CU "inverse tensor-orbit comparison natural transformation component"]
theorem evalFunctorNatTransInv_app
    (L : C) [isInvertibleObject L] (n : ℤ) (A : C) :
    (evalFunctorNatTransInv L n).app A = (evalTensorIso L A n).inv := rfl

/-- The forward and inverse tensor-orbit natural transformations compose to the identity. -/
@[simp, stacks 01CU "tensor-orbit natural transformation forward-inverse law"]
theorem evalFunctorNatTrans_hom_inv_id
    (L : C) [isInvertibleObject L] (n : ℤ) :
    evalFunctorNatTrans L n ≫ evalFunctorNatTransInv L n = 𝟙 _ := by
  ext A
  simp [evalFunctorNatTrans, evalFunctorNatTransInv]

/-- The inverse and forward tensor-orbit natural transformations compose to the identity. -/
@[simp, stacks 01CU "tensor-orbit natural transformation inverse-forward law"]
theorem evalFunctorNatTrans_inv_hom_id
    (L : C) [isInvertibleObject L] (n : ℤ) :
    evalFunctorNatTransInv L n ≫ evalFunctorNatTrans L n = 𝟙 _ := by
  ext A
  simp [evalFunctorNatTrans, evalFunctorNatTransInv]

/-- The forward tensor-orbit comparison followed by its inverse is the identity at every base
object. -/
@[simp, stacks 01CU "tensor-orbit comparison component forward-inverse law"]
theorem evalFunctorNatTrans_app_comp_inv_app
    (L : C) [isInvertibleObject L] (n : ℤ) (A : C) :
    (evalFunctorNatTrans L n).app A ≫
        (evalFunctorNatTransInv L n).app A = 𝟙 _ := by
  simp [evalFunctorNatTrans, evalFunctorNatTransInv]

/-- The inverse tensor-orbit comparison followed by the forward comparison is the identity at
every base object. -/
@[simp, stacks 01CU "tensor-orbit comparison component inverse-forward law"]
theorem evalFunctorNatTransInv_app_comp_app
    (L : C) [isInvertibleObject L] (n : ℤ) (A : C) :
    (evalFunctorNatTransInv L n).app A ≫
        (evalFunctorNatTrans L n).app A = 𝟙 _ := by
  simp [evalFunctorNatTrans, evalFunctorNatTransInv]

/-- The `n`th power of a tensor-right autoequivalence is canonically tensoring on the right by
the `n`th power of its defining object. -/
@[stacks 01CU "tensor-right model of an autoequivalence power"]
noncomputable def evalFunctorIso
    (L : C) [isInvertibleObject L] (n : ℤ) :
    ((tensorRight L).asEquivalence ^ n).functor ≅ tensorRight (obj L n) :=
  { hom := evalFunctorNatTrans L n
    inv := evalFunctorNatTransInv L n
    hom_inv_id := evalFunctorNatTrans_hom_inv_id L n
    inv_hom_id := evalFunctorNatTrans_inv_hom_id L n }

/-- The forward natural transformation of `evalFunctorIso` is the tensor-orbit comparison. -/
@[simp, stacks 01CU "tensor-right model natural isomorphism hom"]
theorem evalFunctorIso_hom
    (L : C) [isInvertibleObject L] (n : ℤ) :
    (evalFunctorIso L n).hom = evalFunctorNatTrans L n := rfl

/-- The inverse natural transformation of `evalFunctorIso` is the named inverse comparison. -/
@[simp, stacks 01CU "tensor-right model natural isomorphism inverse"]
theorem evalFunctorIso_inv
    (L : C) [isInvertibleObject L] (n : ℤ) :
    (evalFunctorIso L n).inv = evalFunctorNatTransInv L n := rfl

/-- The component of `evalFunctorIso` is the objectwise tensor-orbit comparison isomorphism. -/
@[simp, stacks 01CU "tensor-right model natural isomorphism component"]
theorem evalFunctorIso_app
    (L : C) [isInvertibleObject L] (n : ℤ) (A : C) :
    (evalFunctorIso L n).app A = evalTensorIso L A n := by
  ext
  rfl

/-- The forward component of `evalFunctorIso` is the objectwise forward comparison. -/
@[simp, stacks 01CU "tensor-right model natural isomorphism hom component"]
theorem evalFunctorIso_hom_app
    (L : C) [isInvertibleObject L] (n : ℤ) (A : C) :
    (evalFunctorIso L n).hom.app A = (evalTensorIso L A n).hom := rfl

/-- The inverse component of `evalFunctorIso` is the named inverse comparison. -/
@[simp, stacks 01CU "tensor-right model natural isomorphism inverse component"]
theorem evalFunctorIso_inv_app
    (L : C) [isInvertibleObject L] (n : ℤ) (A : C) :
    (evalFunctorIso L n).inv.app A = (evalTensorIso L A n).inv := rfl

/-- Tensoring powers of an invertible object adds their integer degrees. -/
@[stacks 01CU "addition for categorical integral tensor powers"]
noncomputable def addIso
    (L : C) [isInvertibleObject L] (m n : ℤ) :
    obj L m ⊗ obj L n ≅ obj L (m + n) :=
  (evalTensorIso L (obj L m) n).symm ≪≫
    (evalAddIso L (𝟙_ C) m n).symm

/-- The degree-one integral tensor power is canonically the original object. -/
@[stacks 01CU "first categorical integral tensor power"]
noncomputable def oneIso
    (L : C) [isInvertibleObject L] : obj L 1 ≅ L :=
  (rightSuccIso L 0).symm ≪≫
    ((zeroIso L) ▷ᵢ L) ≪≫ λ_ L

/-- Tensoring an integral tensor power on the left by `L` raises its degree by one. This needs no
ambient braiding because both tensor factors are powers of the same invertible object. -/
@[stacks 01CU "left successor for categorical integral tensor powers"]
noncomputable def oneAddIso
    (L : C) [isInvertibleObject L] (n : ℤ) :
    L ⊗ obj L n ≅ obj L (n + 1) :=
  ((oneIso L).symm ▷ᵢ obj L n) ≪≫
    addIso L 1 n ≪≫ indexIso L (Int.add_comm 1 n)

/-- Evaluation of the degree `-1` tensor power. -/
@[stacks 01CU "evaluation of the categorical inverse tensor power"]
noncomputable def evaluationIso
    (L : C) [isInvertibleObject L] :
    L ⊗ obj L (-1) ≅ 𝟙_ C :=
  ((oneIso L).symm ▷ᵢ obj L (-1)) ≪≫
    addIso L 1 (-1) ≪≫ indexIso L Aux.oneAddNegOne ≪≫ zeroIso L

/-- Evaluation with the degree `-1` tensor power on the left. -/
@[stacks 01CU "right evaluation of the categorical inverse tensor power"]
noncomputable def rightEvaluationIso
    (L : C) [isInvertibleObject L] :
    obj L (-1) ⊗ L ≅ 𝟙_ C :=
  rightSuccIso L (-1) ≪≫ zeroIso L

/-- Tensoring by the degree `-1` power lowers an integral tensor degree by one. -/
@[stacks 01CU "predecessor for categorical integral tensor powers"]
noncomputable def minusOneAddIso
    (L : C) [isInvertibleObject L] (n : ℤ) :
    obj L (-1) ⊗ obj L n ≅ obj L (n - 1) :=
  addIso L (-1) n ≪≫ indexIso L (Aux.negOneAdd n)

/-- Each further negative power is the degree `-1` power tensored with the preceding one. -/
@[stacks 01CU "negative successor for categorical integral tensor powers"]
noncomputable def negSuccIso
    (L : C) [isInvertibleObject L] (n : ℕ) :
    obj L (Int.negSucc (n + 1)) ≅
      obj L (-1) ⊗ obj L (Int.negSucc n) :=
  indexIso L (Aux.negSuccEq n) ≪≫
    (addIso L (-1) (Int.negSucc n)).symm

/-- The integral tensor-power addition comparison is associative. -/
theorem addIso_assoc
    (L : C) [isInvertibleObject L] (m n k : ℤ) :
    (addIso L m n ▷ᵢ obj L k) ≪≫ addIso L (m + n) k =
      α_ (obj L m) (obj L n) (obj L k) ≪≫
        (Iso.refl (obj L m) ⊗ᵢ addIso L n k) ≪≫
        addIso L m (n + k) ≪≫ indexIso L (Int.add_assoc m n k).symm := sorry

end CategoryTheory.MonoidalCategory.InvertiblePower

