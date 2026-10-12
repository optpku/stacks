/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left

/-!
# Left Modules and Right Modules over the Opposite DGA

For a left differential graded `A`-module `M`, the right action of `A.opposite` is
`x ⋅ a = (-1)^(deg a * deg x) a x`.  This file packages that Koszul change of handedness on
objects and morphisms and proves that it is an equivalence of ordinary categories.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace LeftDifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra R}

/-- The value of the right `A.opposite`-action induced by a left `A`-action. -/
@[stacks 0FQ0 "Koszul opposite module action"]
def opSmulValue (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x : M.X p) (a : A.X i) : M.X (p + i) :=
  cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_comm i p))
    (CochainDGAlgebra.oppositeSign R i p • M.smul i p a x)

/-- The induced right action is additive in the algebra input. -/
theorem opSmulValue_add_right (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x : M.X p) (a b : A.X i) :
    opSmulValue M p i x (a + b) = opSmulValue M p i x a + opSmulValue M p i x b := sorry

/-- The induced right action is linear in the algebra input. -/
theorem opSmulValue_smul_right (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x : M.X p) (r : R) (a : A.X i) :
    opSmulValue M p i x (r • a) = r • opSmulValue M p i x a := sorry

/-- The induced right action by a fixed module element as a linear map. -/
@[stacks 0FQ0 "linear opposite module action"]
def opSmulRight (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x : M.X p) : A.X i →ₗ[R] M.X (p + i) where
  toFun := opSmulValue M p i x
  map_add' := opSmulValue_add_right M p i x
  map_smul' := opSmulValue_smul_right M p i x

/-- The induced right action is additive in the module input. -/
theorem opSmulRight_add (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x y : M.X p) :
    opSmulRight M p i (x + y) = opSmulRight M p i x + opSmulRight M p i y := sorry

/-- The induced right action is linear in the module input. -/
theorem opSmulRight_smul (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (r : R) (x : M.X p) :
    opSmulRight M p i (r • x) = r • opSmulRight M p i x := sorry

/-- The Koszul-twisted right `A.opposite`-action induced by a left `A`-action. -/
@[stacks 0FQ0 "opposite module action"]
def opSmul (M : LeftDifferentialGradedModule.{u, v} A) (p i : ℤ) :
    M.X p →ₗ[R] A.X i →ₗ[R] M.X (p + i) where
  toFun := opSmulRight M p i
  map_add' := opSmulRight_add M p i
  map_smul' := opSmulRight_smul M p i

/-- The induced right action is the transported Koszul-twisted left action. -/
@[simp] theorem opSmul_apply (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x : M.X p) (a : A.X i) :
    opSmul M p i x a =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_comm i p))
        (CochainDGAlgebra.oppositeSign R i p • M.smul i p a x) := sorry

/-- The differential of the induced right module squares to zero. -/
theorem op_d_sq (M : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : M.X n) : M.d (n + 1) (M.d n x) = 0 := sorry

/-- The induced right action satisfies its unit law. -/
theorem op_smul_one (M : LeftDifferentialGradedModule.{u, v} A)
    (r : R) (p : ℤ) (x : M.X p) :
    opSmul M p 0 x (r • A.opposite.one) =
      cast (DifferentialGradedModule.zeroActionTarget p) (r • x) := sorry

/-- The induced right action respects multiplication in `A.opposite`. -/
theorem op_smul_mul (M : LeftDifferentialGradedModule.{u, v} A)
    (p i j : ℤ) (x : M.X p) (a : A.opposite.X i) (b : A.opposite.X j) :
    opSmul M p (i + j) x (A.opposite.mul i j a b) =
      cast (DifferentialGradedModule.mulActionTarget p i j)
        (opSmul M (p + i) j (opSmul M p i x a) b) := sorry

/-- The induced right action satisfies the right Leibniz rule. -/
theorem op_comm_d (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x : M.X p) (a : A.opposite.X i) :
    M.d (p + i) (opSmul M p i x a) =
      cast (DifferentialGradedModule.dLeftActionTarget p i) (opSmul M (p + 1) i (M.d p x) a) +
        (p.negOnePow : R) •
          cast (DifferentialGradedModule.dRightActionTarget p i)
            (opSmul M p (i + 1) x (A.opposite.d i a)) := sorry

/-- Regard a left differential graded `A`-module as a right differential graded
`A.opposite`-module. -/
@[stacks 0FQ0 "opposite module construction"]
def op (M : LeftDifferentialGradedModule.{u, v} A) :
    DifferentialGradedModule A.opposite where
  X := M.X
  d := M.d
  smul := opSmul M
  d_sq := op_d_sq M
  smul_one := op_smul_one M
  smul_mul := op_smul_mul M
  comm_d := op_comm_d M

/-- Taking the opposite module preserves each homogeneous component. -/
@[simp] theorem op_X (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.op.X n = M.X n := sorry

/-- Taking the opposite module preserves the differential. -/
@[simp] theorem op_d (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    M.op.d n = M.d n := sorry

/-- The right action on the opposite module is the Koszul-twisted left action. -/
@[simp] theorem op_smul_apply (M : LeftDifferentialGradedModule.{u, v} A)
    (p i : ℤ) (x : M.X p) (a : A.opposite.X i) :
    M.op.smul p i x a =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_comm i p))
        (CochainDGAlgebra.oppositeSign R i p • M.smul i p a x) := sorry

/-- The value of the left `A`-action recovered from a right `A.opposite`-action. -/
@[stacks 0FQ0 "recovered opposite module action"]
def unopSmulValue (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a : A.X i) (x : M.X p) : M.X (i + p) :=
  cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_comm p i))
    (CochainDGAlgebra.oppositeSign R i p • M.smul p i x a)

/-- The recovered left action is additive in the module input. -/
theorem unopSmulValue_add_right (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a : A.X i) (x y : M.X p) :
    unopSmulValue M i p a (x + y) =
      unopSmulValue M i p a x + unopSmulValue M i p a y := sorry

/-- The recovered left action is linear in the module input. -/
theorem unopSmulValue_smul_right (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a : A.X i) (r : R) (x : M.X p) :
    unopSmulValue M i p a (r • x) = r • unopSmulValue M i p a x := sorry

/-- The recovered left action by a fixed algebra element as a linear map. -/
@[stacks 0FQ0 "linear recovered opposite module action"]
def unopSmulRight (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a : A.X i) : M.X p →ₗ[R] M.X (i + p) where
  toFun := unopSmulValue M i p a
  map_add' := unopSmulValue_add_right M i p a
  map_smul' := unopSmulValue_smul_right M i p a

/-- The recovered left action is additive in the algebra input. -/
theorem unopSmulRight_add (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a b : A.X i) :
    unopSmulRight M i p (a + b) = unopSmulRight M i p a + unopSmulRight M i p b := sorry

/-- The recovered left action is linear in the algebra input. -/
theorem unopSmulRight_smul (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (r : R) (a : A.X i) :
    unopSmulRight M i p (r • a) = r • unopSmulRight M i p a := sorry

/-- The left `A`-action recovered from a right `A.opposite`-action. -/
@[stacks 0FQ0 "recovered module action"]
def unopSmul (M : DifferentialGradedModule.{u, v} A.opposite) (i p : ℤ) :
    A.X i →ₗ[R] M.X p →ₗ[R] M.X (i + p) where
  toFun := unopSmulRight M i p
  map_add' := unopSmulRight_add M i p
  map_smul' := unopSmulRight_smul M i p

/-- The recovered left action is the transported Koszul-twisted right action. -/
@[simp] theorem unopSmul_apply (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    unopSmul M i p a x =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_comm p i))
        (CochainDGAlgebra.oppositeSign R i p • M.smul p i x a) := sorry

/-- The differential of the recovered left module squares to zero. -/
theorem unop_d_sq (M : DifferentialGradedModule.{u, v} A.opposite)
    (n : ℤ) (x : M.X n) : M.d (n + 1) (M.d n x) = 0 := sorry

/-- The recovered left action satisfies its unit law. -/
theorem unop_smul_one (M : DifferentialGradedModule.{u, v} A.opposite)
    (r : R) (p : ℤ) (x : M.X p) :
    unopSmul M 0 p (r • A.one) x =
      cast (LeftDifferentialGradedModule.zeroActionTarget p) (r • x) := sorry

/-- The recovered left action respects multiplication in `A`. -/
theorem unop_smul_mul (M : DifferentialGradedModule.{u, v} A.opposite)
    (i j p : ℤ) (a : A.X i) (b : A.X j) (x : M.X p) :
    unopSmul M (i + j) p (A.mul i j a b) x =
      cast (LeftDifferentialGradedModule.mulActionTarget p i j)
        (unopSmul M i (j + p) a (unopSmul M j p b x)) := sorry

/-- The recovered left action satisfies the left Leibniz rule. -/
theorem unop_comm_d (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    M.d (i + p) (unopSmul M i p a x) =
      cast (LeftDifferentialGradedModule.dLeftActionTarget p i) (unopSmul M (i + 1) p (A.d i a) x) +
        (i.negOnePow : R) •
          cast (LeftDifferentialGradedModule.dRightActionTarget p i)
            (unopSmul M i (p + 1) a (M.d p x)) := sorry

/-- Recover a left differential graded `A`-module from a right differential graded
    `A.opposite`-module. -/
@[stacks 0FQ0 "inverse opposite module construction"]
def unop (M : DifferentialGradedModule.{u, v} A.opposite) :
    LeftDifferentialGradedModule A where
  X := M.X
  d := M.d
  smul := unopSmul M
  d_sq := unop_d_sq M
  smul_one := unop_smul_one M
  smul_mul := unop_smul_mul M
  comm_d := unop_comm_d M

/-- Recovering the left module preserves each homogeneous component. -/
@[simp] theorem unop_X (M : DifferentialGradedModule.{u, v} A.opposite) (n : ℤ) :
    (unop M).X n = M.X n := sorry

/-- Recovering the left module preserves the differential. -/
@[simp] theorem unop_d (M : DifferentialGradedModule.{u, v} A.opposite) (n : ℤ) :
    (unop M).d n = M.d n := sorry

/-- The recovered left action is the Koszul-twisted right action. -/
@[simp] theorem unop_smul_apply (M : DifferentialGradedModule.{u, v} A.opposite)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    (unop M).smul i p a x =
      cast (congrArg (fun n : ℤ ↦ (M.X n : Type v)) (add_comm p i))
        (CochainDGAlgebra.oppositeSign R i p • M.smul p i x a) := sorry

namespace Hom

/-- A left-module morphism remains differential-compatible after taking opposites. -/
theorem op_comm_d {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : Hom M N) (n : ℤ) (x : M.X n) :
    f.hom (n + 1) (M.op.d n x) = N.op.d n (f.hom n x) := sorry

/-- A left-module morphism is right-linear for the induced opposite actions. -/
theorem op_comm_smul {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : Hom M N) (p i : ℤ) (x : M.X p) (a : A.opposite.X i) :
    f.hom (p + i) (M.op.smul p i x a) =
      N.op.smul p i (f.hom p x) a := sorry

/-- Take the opposite of a left differential graded module morphism. -/
@[stacks 0FQ0 "opposite module morphism"]
def op {M N : LeftDifferentialGradedModule.{u, v} A} (f : Hom M N) :
    DifferentialGradedModule.Hom M.op N.op where
  hom := f.hom
  comm_d := op_comm_d f
  comm_smul := op_comm_smul f

/-- Taking the opposite of a morphism preserves every degreewise linear component. -/
@[simp] theorem op_hom {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : Hom M N) (n : ℤ) : (op f).hom n = f.hom n := sorry

/-- Taking the opposite of a morphism preserves its action on homogeneous elements. -/
@[simp] theorem op_apply {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : Hom M N) (n : ℤ) (x : M.X n) : (op f).hom n x = f.hom n x := sorry

/-- A right `A.opposite`-module morphism remains differential-compatible after recovering the
left action. -/
theorem unop_comm_d {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : DifferentialGradedModule.Hom M N) (n : ℤ) (x : M.X n) :
    f.hom (n + 1) ((LeftDifferentialGradedModule.unop M).d n x) =
      (LeftDifferentialGradedModule.unop N).d n (f.hom n x) := sorry

/-- A right `A.opposite`-module morphism is linear for the recovered left actions. -/
theorem unop_comm_smul {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : DifferentialGradedModule.Hom M N)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    f.hom (i + p) ((LeftDifferentialGradedModule.unop M).smul i p a x) =
      (LeftDifferentialGradedModule.unop N).smul i p a (f.hom p x) := sorry

/-- Recover a left-module morphism from a right `A.opposite`-module morphism. -/
@[stacks 0FQ0 "inverse opposite module morphism"]
def unop {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : DifferentialGradedModule.Hom M N) :
    Hom (LeftDifferentialGradedModule.unop M) (LeftDifferentialGradedModule.unop N) where
  hom := f.hom
  comm_d := unop_comm_d f
  comm_smul := unop_comm_smul f

/-- Recovering a left morphism preserves every degreewise linear component. -/
@[simp] theorem unop_hom {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : DifferentialGradedModule.Hom M N) (n : ℤ) :
    (unop f).hom n = f.hom n := sorry

/-- Recovering a left morphism preserves its action on homogeneous elements. -/
@[simp] theorem unop_apply {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : DifferentialGradedModule.Hom M N) (n : ℤ) (x : M.X n) :
    (unop f).hom n x = f.hom n x := sorry

/-- Taking opposites preserves identity morphisms. -/
theorem op_id (M : LeftDifferentialGradedModule.{u, v} A) :
    op (𝟙 M) = 𝟙 M.op := sorry

/-- Taking opposites preserves composition. -/
theorem op_comp {L M N : LeftDifferentialGradedModule.{u, v} A}
    (f : L ⟶ M) (g : M ⟶ N) :
    op (f ≫ g) = DifferentialGradedModule.Hom.comp (op g) (op f) := sorry

/-- Recovering left morphisms preserves identity morphisms. -/
theorem unop_id (M : DifferentialGradedModule.{u, v} A.opposite) :
    unop (𝟙 M) = 𝟙 (LeftDifferentialGradedModule.unop M) := sorry

/-- Recovering left morphisms preserves composition. -/
theorem unop_comp {L M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : L ⟶ M) (g : M ⟶ N) :
    unop (f ≫ g) = LeftDifferentialGradedModule.Hom.comp (unop g) (unop f) := sorry

end Hom

/-- The functor taking a left `A`-module to its right `A.opposite`-module. -/
@[stacks 0FQ0 "opposite module functor"]
def opFunctor (A : CochainDGAlgebra R) :
    LeftDifferentialGradedModule.{u, v} A ⥤ DifferentialGradedModule A.opposite where
  obj := op
  map := Hom.op
  map_id := Hom.op_id
  map_comp := Hom.op_comp

/-- The opposite-module functor acts on objects by `LeftDifferentialGradedModule.op`. -/
@[simp] theorem opFunctor_obj (M : LeftDifferentialGradedModule.{u, v} A) :
    (opFunctor A).obj M = M.op := sorry

/-- The opposite-module functor acts on morphisms by `LeftDifferentialGradedModule.Hom.op`. -/
@[simp] theorem opFunctor_map {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    (opFunctor A).map f = Hom.op f := sorry

/-- The opposite-module functor preserves the degreewise map of every morphism. -/
@[simp] theorem opFunctor_map_hom {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (n : ℤ) : ((opFunctor A).map f).hom n = f.hom n := sorry

/-- The opposite-module functor preserves the value of every morphism component. -/
@[simp] theorem opFunctor_map_apply {M N : LeftDifferentialGradedModule.{u, v} A}
    (f : M ⟶ N) (n : ℤ) (x : M.X n) : ((opFunctor A).map f).hom n x = f.hom n x := sorry

/-- The functor recovering a left `A`-module from a right `A.opposite`-module. -/
@[stacks 0FQ0 "inverse opposite module functor"]
def unopFunctor (A : CochainDGAlgebra R) :
    DifferentialGradedModule.{u, v} A.opposite ⥤ LeftDifferentialGradedModule A where
  obj := unop
  map := Hom.unop
  map_id := Hom.unop_id
  map_comp := Hom.unop_comp

/-- The inverse opposite-module functor acts on objects by
`LeftDifferentialGradedModule.unop`. -/
@[simp] theorem unopFunctor_obj (M : DifferentialGradedModule.{u, v} A.opposite) :
    (unopFunctor A).obj M = unop M := sorry

/-- The inverse opposite-module functor acts on morphisms by
`LeftDifferentialGradedModule.Hom.unop`. -/
@[simp] theorem unopFunctor_map {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : M ⟶ N) : (unopFunctor A).map f = Hom.unop f := sorry

/-- The inverse opposite-module functor preserves the degreewise map of every morphism. -/
@[simp] theorem unopFunctor_map_hom {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : M ⟶ N) (n : ℤ) : ((unopFunctor A).map f).hom n = f.hom n := sorry

/-- The inverse opposite-module functor preserves the value of every morphism component. -/
@[simp] theorem unopFunctor_map_apply
    {M N : DifferentialGradedModule.{u, v} A.opposite}
    (f : M ⟶ N) (n : ℤ) (x : M.X n) :
    ((unopFunctor A).map f).hom n x = f.hom n x := sorry

/-- The identity-shaped unit morphism commutes with differentials. -/
theorem unitHom_comm_d (M : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : M.X n) :
    (LinearMap.id : M.X (n + 1) →ₗ[R] M.X (n + 1)) (M.d n x) =
      (unop M.op).d n ((LinearMap.id : M.X n →ₗ[R] M.X n) x) := sorry

/-- The identity-shaped unit morphism commutes with left actions. -/
theorem unitHom_comm_smul (M : LeftDifferentialGradedModule.{u, v} A)
    (i p : ℤ) (a : A.X i) (x : M.X p) :
    (LinearMap.id : M.X (i + p) →ₗ[R] M.X (i + p)) (M.smul i p a x) =
      (unop M.op).smul i p a ((LinearMap.id : M.X p →ₗ[R] M.X p) x) := sorry

/-- The unit morphism from a left module to the double handedness change. -/
def unitHom (M : LeftDifferentialGradedModule.{u, v} A) : M ⟶ unop M.op where
  hom _ := LinearMap.id
  comm_d := unitHom_comm_d M
  comm_smul := unitHom_comm_smul M

/-- The unit morphism is degreewise the identity linear map. -/
@[simp] theorem unitHom_hom (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    (unitHom M).hom n = LinearMap.id := sorry

/-- The unit morphism fixes every homogeneous element. -/
@[simp] theorem unitHom_apply (M : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : M.X n) : (unitHom M).hom n x = x := sorry

/-- The identity-shaped inverse unit morphism commutes with differentials. -/
theorem unitInv_comm_d (M : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : (unop M.op).X n) :
    (LinearMap.id : (unop M.op).X (n + 1) →ₗ[R] M.X (n + 1))
        ((unop M.op).d n x) =
      M.d n ((LinearMap.id : (unop M.op).X n →ₗ[R] M.X n) x) := sorry

/-- The identity-shaped inverse unit morphism commutes with left actions. -/
theorem unitInv_comm_smul (M : LeftDifferentialGradedModule.{u, v} A)
    (i p : ℤ) (a : A.X i) (x : (unop M.op).X p) :
    (LinearMap.id : (unop M.op).X (i + p) →ₗ[R] M.X (i + p))
        ((unop M.op).smul i p a x) =
      M.smul i p a ((LinearMap.id : (unop M.op).X p →ₗ[R] M.X p) x) := sorry

/-- The inverse of the unit morphism. -/
def unitInv (M : LeftDifferentialGradedModule.{u, v} A) : unop M.op ⟶ M where
  hom _ := LinearMap.id
  comm_d := unitInv_comm_d M
  comm_smul := unitInv_comm_smul M

/-- The inverse unit morphism is degreewise the identity linear map. -/
@[simp] theorem unitInv_hom (M : LeftDifferentialGradedModule.{u, v} A) (n : ℤ) :
    (unitInv M).hom n = LinearMap.id := sorry

/-- The inverse unit morphism fixes every homogeneous element. -/
@[simp] theorem unitInv_apply (M : LeftDifferentialGradedModule.{u, v} A)
    (n : ℤ) (x : (unop M.op).X n) : (unitInv M).hom n x = x := sorry

/-- The unit morphism followed by its inverse is the identity. -/
theorem unit_hom_inv_id (M : LeftDifferentialGradedModule.{u, v} A) :
    unitHom M ≫ unitInv M = 𝟙 M := sorry

/-- The inverse unit morphism followed by the unit is the identity. -/
theorem unit_inv_hom_id (M : LeftDifferentialGradedModule.{u, v} A) :
    unitInv M ≫ unitHom M = 𝟙 (unop M.op) := sorry

/-- The double handedness change is naturally isomorphic to the original left module. -/
@[stacks 0FQ0 "unit of the opposite module equivalence"]
def unitIso (M : LeftDifferentialGradedModule.{u, v} A) : M ≅ unop M.op where
  hom := unitHom M
  inv := unitInv M
  hom_inv_id := unit_hom_inv_id M
  inv_hom_id := unit_inv_hom_id M

/-- The identity-shaped counit morphism commutes with differentials. -/
theorem counitHom_comm_d (M : DifferentialGradedModule.{u, v} A.opposite)
    (n : ℤ) (x : (unop M).op.X n) :
    (LinearMap.id : (unop M).op.X (n + 1) →ₗ[R] M.X (n + 1))
        ((unop M).op.d n x) =
      M.d n ((LinearMap.id : (unop M).op.X n →ₗ[R] M.X n) x) := sorry

/-- The identity-shaped counit morphism commutes with right actions. -/
theorem counitHom_comm_smul (M : DifferentialGradedModule.{u, v} A.opposite)
    (p i : ℤ) (x : (unop M).op.X p) (a : A.opposite.X i) :
    (LinearMap.id : (unop M).op.X (p + i) →ₗ[R] M.X (p + i))
        ((unop M).op.smul p i x a) =
      M.smul p i ((LinearMap.id : (unop M).op.X p →ₗ[R] M.X p) x) a := sorry

/-- The counit morphism from the double handedness change to a right module. -/
def counitHom (M : DifferentialGradedModule.{u, v} A.opposite) : (unop M).op ⟶ M where
  hom _ := LinearMap.id
  comm_d := counitHom_comm_d M
  comm_smul := counitHom_comm_smul M

/-- The counit morphism is degreewise the identity linear map. -/
@[simp] theorem counitHom_hom
    (M : DifferentialGradedModule.{u, v} A.opposite) (n : ℤ) :
    (counitHom M).hom n = LinearMap.id := sorry

/-- The counit morphism fixes every homogeneous element. -/
@[simp] theorem counitHom_apply
    (M : DifferentialGradedModule.{u, v} A.opposite)
    (n : ℤ) (x : (unop M).op.X n) : (counitHom M).hom n x = x := sorry

/-- The identity-shaped inverse counit morphism commutes with differentials. -/
theorem counitInv_comm_d (M : DifferentialGradedModule.{u, v} A.opposite)
    (n : ℤ) (x : M.X n) :
    (LinearMap.id : M.X (n + 1) →ₗ[R] (unop M).op.X (n + 1)) (M.d n x) =
      (unop M).op.d n
        ((LinearMap.id : M.X n →ₗ[R] (unop M).op.X n) x) := sorry

/-- The identity-shaped inverse counit morphism commutes with right actions. -/
theorem counitInv_comm_smul (M : DifferentialGradedModule.{u, v} A.opposite)
    (p i : ℤ) (x : M.X p) (a : A.opposite.X i) :
    (LinearMap.id : M.X (p + i) →ₗ[R] (unop M).op.X (p + i)) (M.smul p i x a) =
      (unop M).op.smul p i
        ((LinearMap.id : M.X p →ₗ[R] (unop M).op.X p) x) a := sorry

/-- The inverse of the counit morphism. -/
def counitInv (M : DifferentialGradedModule.{u, v} A.opposite) : M ⟶ (unop M).op where
  hom _ := LinearMap.id
  comm_d := counitInv_comm_d M
  comm_smul := counitInv_comm_smul M

/-- The inverse counit morphism is degreewise the identity linear map. -/
@[simp] theorem counitInv_hom
    (M : DifferentialGradedModule.{u, v} A.opposite) (n : ℤ) :
    (counitInv M).hom n = LinearMap.id := sorry

/-- The inverse counit morphism fixes every homogeneous element. -/
@[simp] theorem counitInv_apply
    (M : DifferentialGradedModule.{u, v} A.opposite)
    (n : ℤ) (x : M.X n) : (counitInv M).hom n x = x := sorry

/-- The counit morphism followed by its inverse is the identity. -/
theorem counit_hom_inv_id (M : DifferentialGradedModule.{u, v} A.opposite) :
    counitHom M ≫ counitInv M = 𝟙 ((unop M).op) := sorry

/-- The inverse counit morphism followed by the counit is the identity. -/
theorem counit_inv_hom_id (M : DifferentialGradedModule.{u, v} A.opposite) :
    counitInv M ≫ counitHom M = 𝟙 M := sorry

/-- The double handedness change is naturally isomorphic to the original right module. -/
@[stacks 0FQ0 "counit of the opposite module equivalence"]
def counitIso (M : DifferentialGradedModule.{u, v} A.opposite) : (unop M).op ≅ M where
  hom := counitHom M
  inv := counitInv M
  hom_inv_id := counit_hom_inv_id M
  inv_hom_id := counit_inv_hom_id M

/-- Naturality of the unit isomorphisms. -/
theorem unitIso_naturality {M N : LeftDifferentialGradedModule.{u, v} A} (f : M ⟶ N) :
    f ≫ (unitIso N).hom =
      (unitIso M).hom ≫ (opFunctor A ⋙ unopFunctor A).map f := sorry

/-- Naturality of the counit isomorphisms. -/
theorem counitIso_naturality
    {M N : DifferentialGradedModule.{u, v} A.opposite} (f : M ⟶ N) :
    (unopFunctor A ⋙ opFunctor A).map f ≫ (counitIso N).hom =
      (counitIso M).hom ≫ f := sorry

/-- Lemma 22.11.2 (0FQ0): changing handedness with the Koszul sign is an equivalence from left
differential graded `A`-modules to right differential graded `A.opposite`-modules. -/
@[stacks 0FQ0]
def opEquivalence (A : CochainDGAlgebra R) :
    LeftDifferentialGradedModule.{u, v} A ≌ DifferentialGradedModule A.opposite where
  functor := opFunctor A
  inverse := unopFunctor A
  unitIso := NatIso.ofComponents unitIso unitIso_naturality
  counitIso := NatIso.ofComponents counitIso counitIso_naturality

namespace opEquivalence

/-- The forward functor of the handedness-change equivalence. -/
@[simp] theorem functor_eq (A : CochainDGAlgebra R) :
    (opEquivalence.{u, v} A).functor = opFunctor A := sorry

/-- The inverse functor of the handedness-change equivalence. -/
@[simp] theorem inverse_eq (A : CochainDGAlgebra R) :
    (opEquivalence.{u, v} A).inverse = unopFunctor A := sorry

/-- The unit component of the handedness-change equivalence is the explicit identity-shaped
isomorphism. -/
@[simp] theorem unitIso_app (A : CochainDGAlgebra R)
    (M : LeftDifferentialGradedModule.{u, v} A) :
    (opEquivalence A).unitIso.app M = unitIso M := sorry

/-- The counit component of the handedness-change equivalence is the explicit identity-shaped
isomorphism. -/
@[simp] theorem counitIso_app (A : CochainDGAlgebra R)
    (M : DifferentialGradedModule.{u, v} A.opposite) :
    (opEquivalence A).counitIso.app M = counitIso M := sorry

end opEquivalence

namespace opFunctor

/-- The change-of-handedness functor is an equivalence. -/
instance isEquivalence (A : CochainDGAlgebra R) :
    (opFunctor A : LeftDifferentialGradedModule.{u, v} A ⥤
      DifferentialGradedModule A.opposite).IsEquivalence := sorry

end opFunctor

namespace unopFunctor

/-- The inverse change-of-handedness functor is an equivalence. -/
instance isEquivalence (A : CochainDGAlgebra R) :
    (unopFunctor A : DifferentialGradedModule.{u, v} A.opposite ⥤
      LeftDifferentialGradedModule A).IsEquivalence := sorry

end unopFunctor

end LeftDifferentialGradedModule
