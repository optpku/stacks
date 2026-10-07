module

public import ReasLib.Algebra.Homology.CochainDGAlgebra.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual

/-!
# Pontryagin duals of right differential graded modules

This file supplies the handedness-dual counterpart of
`LeftDifferentialGradedModule.pontryaginDual`.  The Koszul sign in the induced left action is
part of the concrete data, as required for double-dual evaluation and the representability of
cohomology by shifts of `Aᵛ`.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

namespace Pontryagin

/-- The target degree of the differential on the Pontryagin dual. -/
@[stacks 0FQD "degree transport for the right Pontryagin-dual differential"]
theorem dIndex (n : ℤ) : -(n + 1) + 1 = -n :=
  (congrArg (fun z : ℤ ↦ z + 1) (neg_add n 1)).trans (neg_add_cancel_right (-n) 1)

/-- The target degree of right multiplication used in the dual left action. -/
@[stacks 0FQD "degree transport for the right Pontryagin-dual action"]
theorem actionIndex (i p : ℤ) : -(i + p) + i = -p :=
  (congrArg (fun z : ℤ ↦ z + i) (neg_add_rev i p)).trans (neg_add_cancel_right (-p) i)

/-- Negating a cohomological degree twice returns the original degree. -/
@[stacks 0FQD "double-negation transport for Pontryagin evaluation"]
theorem doubleDualIndex (n : ℤ) : -(-n) = n := neg_neg n

/-- The differential on the character dual of a right DG module. -/
@[stacks 0FQD "right-dual differential"]
def d (M : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    CharacterModule (M.X (-n)) →ₗ[R] CharacterModule (M.X (-(n + 1))) :=
  (-(n.negOnePow : R)) • CharacterModule.dual
    (ModuleCat.castLinearMap (congrArg M.X (dIndex n)) (M.d (-(n + 1))))

/-- Right multiplication by a fixed homogeneous algebra element, with its target reindexed for
the dual left action. -/
@[stacks 0FQD "right-dual action transport"]
def rightAction (M : DifferentialGradedModule.{u, w} A)
    (i p : ℤ) (a : A.X i) : M.X (-(i + p)) →ₗ[R] M.X (-p) :=
  ModuleCat.castLinearMap (congrArg M.X (actionIndex i p))
    ((M.smul (-(i + p)) i).flip a)

/-- The value of the Koszul-signed left action on the character dual of a right DG module. -/
@[stacks 0FQD "right-dual action value"]
def actionValue (M : DifferentialGradedModule.{u, w} A)
    (i p : ℤ) (a : A.X i) (f : CharacterModule (M.X (-p))) :
    CharacterModule (M.X (-(i + p))) :=
  CochainDGAlgebra.oppositeSign R i p • CharacterModule.dual (rightAction M i p a) f

/-- The dual left action is additive in the character variable. -/
theorem actionValue_add_right (M : DifferentialGradedModule.{u, w} A)
    (i p : ℤ) (a : A.X i) (f g : CharacterModule (M.X (-p))) :
    actionValue M i p a (f + g) = actionValue M i p a f + actionValue M i p a g := sorry

/-- The dual left action is linear in the character variable. -/
theorem actionValue_smul_right (M : DifferentialGradedModule.{u, w} A)
    (i p : ℤ) (a : A.X i) (r : R) (f : CharacterModule (M.X (-p))) :
    actionValue M i p a (r • f) = r • actionValue M i p a f := sorry

/-- The dual left action by a fixed homogeneous algebra element. -/
@[stacks 0FQD "right-dual action map"]
def actionRight (M : DifferentialGradedModule.{u, w} A)
    (i p : ℤ) (a : A.X i) :
    CharacterModule (M.X (-p)) →ₗ[R] CharacterModule (M.X (-(i + p))) where
  toFun := actionValue M i p a
  map_add' := actionValue_add_right M i p a
  map_smul' := actionValue_smul_right M i p a

/-- The dual left action is additive in the algebra variable. -/
theorem actionRight_add (M : DifferentialGradedModule.{u, w} A)
    (i p : ℤ) (a b : A.X i) :
    actionRight M i p (a + b) = actionRight M i p a + actionRight M i p b := sorry

/-- The dual left action is linear in the algebra variable. -/
theorem actionRight_smul (M : DifferentialGradedModule.{u, w} A)
    (i p : ℤ) (r : R) (a : A.X i) :
    actionRight M i p (r • a) = r • actionRight M i p a := sorry

/-- The Koszul-signed homogeneous left action on the Pontryagin dual of a right DG module. -/
@[stacks 0FQD "right-dual homogeneous action"]
def action (M : DifferentialGradedModule.{u, w} A) (i p : ℤ) :
    A.X i →ₗ[R] CharacterModule (M.X (-p)) →ₗ[R]
      CharacterModule (M.X (-(i + p))) where
  toFun := actionRight M i p
  map_add' := actionRight_add M i p
  map_smul' := actionRight_smul M i p

end Pontryagin

/-- Section 22.19 (0FQD): the Pontryagin dual of a right differential graded `A`-module, as a
left differential graded `A`-module. -/
@[stacks 0FQD "Pontryagin dual of a right differential graded module"]
def pontryaginDual (M : DifferentialGradedModule.{u, w} A) :
    LeftDifferentialGradedModule.{u, w} A where
  X n := ModuleCat.of R (CharacterModule (M.X (-n)))
  d := Pontryagin.d M
  smul := Pontryagin.action M
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` component of the Pontryagin dual is the character module of degree `-n`. -/
@[simp]
theorem pontryaginDual_X (M : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    M.pontryaginDual.X n = ModuleCat.of R (CharacterModule (M.X (-n))) := sorry

/-- The differential on the right-to-left Pontryagin dual is the standard Hom differential. -/
@[simp]
theorem pontryaginDual_d (M : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    M.pontryaginDual.d n = Pontryagin.d M n := sorry

/-- The induced left action includes the Koszul sign `(-1)^(i * p)`. -/
@[simp]
theorem pontryaginDual_smul (M : DifferentialGradedModule.{u, w} A) (i p : ℤ) :
    M.pontryaginDual.smul i p = Pontryagin.action M i p := sorry

/-- A right-DG-module morphism induces a left-DG-module morphism on Pontryagin duals in the
reverse direction. -/
@[stacks 0FQD "map on right character duals"]
def pontryaginDualMap {M N : DifferentialGradedModule.{u, w} A} (f : M ⟶ N) :
    N.pontryaginDual ⟶ M.pontryaginDual where
  hom n := CharacterModule.dual (f.hom (-n))
  comm_d := sorry
  comm_smul := sorry

/-- The map on right-module Pontryagin duals is degreewise precomposition. -/
@[simp]
theorem pontryaginDualMap_hom {M N : DifferentialGradedModule.{u, w} A}
    (f : M ⟶ N) (n : ℤ) :
    (pontryaginDualMap f).hom n = CharacterModule.dual (f.hom (-n)) := sorry

/-- Pontryagin duality is a contravariant functor from right to left differential graded
modules. -/
@[stacks 0FQD "right-to-left Pontryagin duality functor"]
def pontryaginDualFunctor (A : CochainDGAlgebra.{u, v} R) :
    (DifferentialGradedModule.{u, w} A)ᵒᵖ ⥤
      LeftDifferentialGradedModule.{u, w} A where
  obj M := M.unop.pontryaginDual
  map f := pontryaginDualMap f.unop
  map_id := sorry
  map_comp := sorry

/-- A degreewise injective morphism becomes degreewise surjective after Pontryagin duality. -/
theorem pontryaginDualMap_surjective {M N : DifferentialGradedModule.{u, w} A}
    (f : M ⟶ N) (hf : ∀ n : ℤ, Function.Injective (f.hom n)) (n : ℤ) :
    Function.Surjective ((pontryaginDualMap f).hom n) := sorry

/-- A degreewise surjective morphism becomes degreewise injective after Pontryagin duality. -/
theorem pontryaginDualMap_injective {M N : DifferentialGradedModule.{u, w} A}
    (f : M ⟶ N) (hf : ∀ n : ℤ, Function.Surjective (f.hom n)) (n : ℤ) :
    Function.Injective ((pontryaginDualMap f).hom n) := sorry

namespace Pontryagin

/-- Signed evaluation of a homogeneous element in its character double dual. -/
@[stacks 0FQD "double-dual evaluation value"]
def evaluationValue (M : DifferentialGradedModule.{u, w} A)
    (n : ℤ) (x : M.X n) : CharacterModule (M.pontryaginDual.X (-n)) where
  toFun f :=
    (cast
      (congrArg (fun Q : ModuleCat.{w} R ↦ (Q : Type w))
        (pontryaginDual_X M (-n))) f)
      (cast (congrArg (fun k : ℤ ↦ (M.X k : Type w)) (doubleDualIndex n).symm)
        ((n.negOnePow : R) • x))
  map_zero' := sorry
  map_add' := sorry

/-- Signed double-dual evaluation is additive in the original module element. -/
theorem evaluationValue_add (M : DifferentialGradedModule.{u, w} A)
    (n : ℤ) (x y : M.X n) :
    evaluationValue M n (x + y) = evaluationValue M n x + evaluationValue M n y := sorry

/-- Signed double-dual evaluation is linear in the original module element. -/
theorem evaluationValue_smul (M : DifferentialGradedModule.{u, w} A)
    (n : ℤ) (r : R) (x : M.X n) :
    evaluationValue M n (r • x) = r • evaluationValue M n x := sorry

/-- The degree-`n` linear map underlying double-dual evaluation. -/
@[stacks 0FQD "double-dual evaluation map"]
def evaluationHom (M : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    M.X n →ₗ[R] CharacterModule (M.pontryaginDual.X (-n)) where
  toFun := evaluationValue M n
  map_add' := evaluationValue_add M n
  map_smul' := evaluationValue_smul M n

end Pontryagin

/-- Section 22.19 (0FQD): the signed evaluation morphism from a right DG module to its
Pontryagin double dual. -/
@[stacks 0FQD "Pontryagin double-dual evaluation"]
def pontryaginEvaluation (M : DifferentialGradedModule.{u, w} A) :
    M ⟶ LeftDifferentialGradedModule.pontryaginDual M.pontryaginDual where
  hom := Pontryagin.evaluationHom M
  comm_d := sorry
  comm_smul := sorry

/-- Pontryagin double-dual evaluation is degreewise injective. -/
@[stacks 0FQD "injectivity of double-dual evaluation"]
theorem pontryaginEvaluation_injective (M : DifferentialGradedModule.{u, w} A) (n : ℤ) :
    Function.Injective ((pontryaginEvaluation M).hom n) := sorry

/-- Pontryagin double-dual evaluation is a monomorphism of right DG modules. -/
@[stacks 0FQD "double-dual evaluation monomorphism"]
instance pontryaginEvaluationMono (M : DifferentialGradedModule.{u, w} A) :
    Mono (pontryaginEvaluation M) := sorry

end DifferentialGradedModule
