module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Regular

/-!
# Pontryagin duals of differential graded modules

This file constructs the character dual of a left differential graded module as a right
differential graded module.  The construction is contravariantly functorial and supplies the
distinguished right module `Aᵛ` used by property I.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory

namespace LeftDifferentialGradedModule

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- The target degree of the differential on the character dual. -/
@[stacks 0FQD "degree transport for the Pontryagin-dual differential"]
theorem pontryaginDual_d_index (n : ℤ) : -(n + 1) + 1 = -n :=
  (congrArg (fun z : ℤ ↦ z + 1) (neg_add n 1)).trans (neg_add_cancel_right (-n) 1)

/-- The target degree of the left action used to define the right action on the character
dual. -/
@[stacks 0FQD "degree transport for the Pontryagin-dual action"]
theorem pontryaginDual_smul_index (p i : ℤ) : i + -(p + i) = -p :=
  (congrArg (fun z : ℤ ↦ i + z) (neg_add_rev p i)).trans
    (add_neg_cancel_left i (-p))

/-- The differential on the character dual, namely `-(-1)^n` times precomposition with the
differential of the original module. -/
@[stacks 0FQD "character-dual differential"]
def pontryaginDualD (M : LeftDifferentialGradedModule.{u, w} A) (n : ℤ) :
    CharacterModule (M.X (-n)) →ₗ[R] CharacterModule (M.X (-(n + 1))) :=
  (-(n.negOnePow : R)) • CharacterModule.dual
    (ModuleCat.castLinearMap (congrArg M.X (pontryaginDual_d_index n)) (M.d (-(n + 1))))

/-- The value of the right action on the character dual, obtained by precomposition with the
left action on the original module. -/
@[stacks 0FQD "character-dual action value"]
def pontryaginDualSmulValue (M : LeftDifferentialGradedModule.{u, w} A)
    (p i : ℤ) (f : CharacterModule (M.X (-p))) (a : A.X i) :
    CharacterModule (M.X (-(p + i))) :=
  CharacterModule.dual
    (ModuleCat.castLinearMap (congrArg M.X (pontryaginDual_smul_index p i))
      (M.smul i (-(p + i)) a)) f

/-- The character-dual action is additive in the algebra variable. -/
theorem pontryaginDualSmulValue_add_right
    (M : LeftDifferentialGradedModule.{u, w} A) (p i : ℤ)
    (f : CharacterModule (M.X (-p))) (a b : A.X i) :
    pontryaginDualSmulValue M p i f (a + b) =
      pontryaginDualSmulValue M p i f a + pontryaginDualSmulValue M p i f b := sorry

/-- The character-dual action is linear in the algebra variable. -/
theorem pontryaginDualSmulValue_smul_right
    (M : LeftDifferentialGradedModule.{u, w} A) (p i : ℤ)
    (f : CharacterModule (M.X (-p))) (r : R) (a : A.X i) :
    pontryaginDualSmulValue M p i f (r • a) =
      r • pontryaginDualSmulValue M p i f a := sorry

/-- Right multiplication by a fixed character in the Pontryagin dual. -/
@[stacks 0FQD "character-dual right action map"]
def pontryaginDualSmulRight (M : LeftDifferentialGradedModule.{u, w} A)
    (p i : ℤ) (f : CharacterModule (M.X (-p))) :
    A.X i →ₗ[R] CharacterModule (M.X (-(p + i))) where
  toFun := pontryaginDualSmulValue M p i f
  map_add' := pontryaginDualSmulValue_add_right M p i f
  map_smul' := pontryaginDualSmulValue_smul_right M p i f

/-- The character-dual action is additive in the character variable. -/
theorem pontryaginDualSmulRight_add
    (M : LeftDifferentialGradedModule.{u, w} A) (p i : ℤ)
    (f g : CharacterModule (M.X (-p))) :
    pontryaginDualSmulRight M p i (f + g) =
      pontryaginDualSmulRight M p i f + pontryaginDualSmulRight M p i g := sorry

/-- The character-dual action is linear in the character variable. -/
theorem pontryaginDualSmulRight_smul
    (M : LeftDifferentialGradedModule.{u, w} A) (p i : ℤ)
    (r : R) (f : CharacterModule (M.X (-p))) :
    pontryaginDualSmulRight M p i (r • f) =
      r • pontryaginDualSmulRight M p i f := sorry

/-- The homogeneous right action on the Pontryagin dual of a left DG module. -/
@[stacks 0FQD "character-dual homogeneous action"]
def pontryaginDualSmul (M : LeftDifferentialGradedModule.{u, w} A) (p i : ℤ) :
    CharacterModule (M.X (-p)) →ₗ[R]
      A.X i →ₗ[R] CharacterModule (M.X (-(p + i))) where
  toFun := pontryaginDualSmulRight M p i
  map_add' := pontryaginDualSmulRight_add M p i
  map_smul' := pontryaginDualSmulRight_smul M p i

/-- Section 22.19 (0FQD): the Pontryagin dual of a left differential graded `A`-module, as a
right differential graded `A`-module. -/
@[stacks 0FQD "Pontryagin dual of a left differential graded module"]
def pontryaginDual (M : LeftDifferentialGradedModule.{u, w} A) :
    DifferentialGradedModule.{u, w} A where
  X n := ModuleCat.of R (CharacterModule (M.X (-n)))
  d := pontryaginDualD M
  smul := pontryaginDualSmul M
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- The degree-`n` component of the Pontryagin dual is the character module of degree `-n`. -/
@[simp]
theorem pontryaginDual_X (M : LeftDifferentialGradedModule.{u, w} A) (n : ℤ) :
    (pontryaginDual M).X n = ModuleCat.of R (CharacterModule (M.X (-n))) := sorry

/-- The differential of the Pontryagin dual is explicit precomposition with the original
differential, with the Hom-complex sign. -/
@[simp]
theorem pontryaginDual_d (M : LeftDifferentialGradedModule.{u, w} A) (n : ℤ) :
    (pontryaginDual M).d n = pontryaginDualD M n := sorry

/-- The right action on the Pontryagin dual is explicit precomposition with the original left
action. -/
@[simp]
theorem pontryaginDual_smul (M : LeftDifferentialGradedModule.{u, w} A) (p i : ℤ) :
    (pontryaginDual M).smul p i = pontryaginDualSmul M p i := sorry

/-- A left-DG-module morphism induces a morphism of Pontryagin duals in the reverse direction. -/
@[stacks 0FQD "map on character duals"]
def pontryaginDualMap {M N : LeftDifferentialGradedModule.{u, w} A} (f : M ⟶ N) :
    pontryaginDual N ⟶ pontryaginDual M where
  hom n := CharacterModule.dual (f.hom (-n))
  comm_d := sorry
  comm_smul := sorry

/-- The map on Pontryagin duals is degreewise precomposition. -/
@[simp]
theorem pontryaginDualMap_hom {M N : LeftDifferentialGradedModule.{u, w} A}
    (f : M ⟶ N) (n : ℤ) :
    (pontryaginDualMap f).hom n = CharacterModule.dual (f.hom (-n)) := sorry

/-- Pontryagin duality is a contravariant functor from left to right differential graded
modules. -/
@[stacks 0FQD "Pontryagin duality functor"]
def pontryaginDualFunctor (A : CochainDGAlgebra.{u, v} R) :
    (LeftDifferentialGradedModule.{u, w} A)ᵒᵖ ⥤
      DifferentialGradedModule.{u, w} A where
  obj M := pontryaginDual M.unop
  map f := pontryaginDualMap f.unop
  map_id := sorry
  map_comp := sorry

end LeftDifferentialGradedModule

namespace CochainDGAlgebra

variable {R : Type u} [CommRing R]

/-- Section 22.19 (0FQD): the distinguished Pontryagin-dual right DG module `Aᵛ`. -/
@[stacks 0FQD "dual regular differential graded module"]
def dualRegularModule (A : CochainDGAlgebra.{u, v} R) :
    DifferentialGradedModule.{u, v} A :=
  LeftDifferentialGradedModule.pontryaginDual A.leftRegularModule

/-- The degree-`n` component of `Aᵛ` is `Hom_ℤ(A^{-n}, ℚ/ℤ)`. -/
@[simp]
theorem dualRegularModule_X (A : CochainDGAlgebra.{u, v} R) (n : ℤ) :
    A.dualRegularModule.X n = ModuleCat.of R (CharacterModule (A.X (-n))) := sorry

end CochainDGAlgebra

/-- Reusable notation for the distinguished Pontryagin-dual right DG module. -/
scoped[DifferentialGradedModule] postfix:max "ᵛ" => CochainDGAlgebra.dualRegularModule

open scoped DifferentialGradedModule
