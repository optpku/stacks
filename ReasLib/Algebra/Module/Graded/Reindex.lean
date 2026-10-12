/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Module.GradedModule
public import Mathlib.GroupTheory.GroupAction.Hom
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v w x y z

namespace DirectSum.Gmodule

variable {ι : Type u} {κ : Type v} {κprime : Type w}
variable {A : ι → Type x} {M : κ → Type y} {N : κ → Type z}
variable [AddMonoid ι] [VAdd ι κ] [VAdd ι κprime]
variable [∀ i, AddMonoid (A i)] [∀ j, AddMonoid (M j)] [∀ j, AddMonoid (N j)]
variable [GradedMonoid.GMonoid A]

/-- The homogeneous action transported along an equivariant reindexing of module degrees. -/
@[reducible, stacks 01CV "homogeneous action under equivariant degree reindexing"]
def reindexSmul (e : κprime →[ι] κ) (M : κ → Type y) [∀ j, AddMonoid (M j)]
    [Gmodule A M] {i : ι} {j : κprime} (a : A i) (x : M (e j)) : M (e (i +ᵥ j)) :=
  Eq.mp (congrArg M (e.map_vadd i j).symm)
    (@GradedMonoid.GSMul.smul ι κ A M _ _ i (e j) a x)

/-- The induced scalar operation on the sigma type of reindexed homogeneous pieces. -/
@[reducible, stacks 01CV "total homogeneous action under degree reindexing"]
def reindexTotalSmul (e : κprime →[ι] κ) (M : κ → Type y) [∀ j, AddMonoid (M j)]
    [Gmodule A M] (a : GradedMonoid A)
    (x : GradedMonoid (fun j : κprime ↦ M (e j))) :
    GradedMonoid (fun j : κprime ↦ M (e j)) :=
  ⟨a.1 +ᵥ x.1, reindexSmul e M a.2 x.2⟩

/-- The degree-zero unit is neutral for the reindexed homogeneous action. -/
@[stacks 01CV "unit law for equivariant degree reindexing"]
theorem reindex_one_smul (e : κprime →[ι] κ) (M : κ → Type y)
    [∀ j, AddMonoid (M j)] [Gmodule A M]
    (x : GradedMonoid (fun j : κprime ↦ M (e j))) :
    reindexTotalSmul e M (1 : GradedMonoid A) x = x := sorry

/-- Multiplication of homogeneous scalars is associative with the reindexed action. -/
@[stacks 01CV "multiplication law for equivariant degree reindexing"]
theorem reindex_mul_smul (e : κprime →[ι] κ) (M : κ → Type y)
    [∀ j, AddMonoid (M j)] [Gmodule A M]
    (a b : GradedMonoid A) (x : GradedMonoid (fun j : κprime ↦ M (e j))) :
    reindexTotalSmul e M (a * b) x =
      reindexTotalSmul e M a (reindexTotalSmul e M b x) := sorry

/-- The reindexed homogeneous action distributes over addition in a module piece. -/
@[stacks 01CV "additivity in a reindexed module piece"]
theorem reindex_smul_add (e : κprime →[ι] κ) (M : κ → Type y)
    [∀ j, AddMonoid (M j)] [Gmodule A M] {i : ι} {j : κprime}
    (a : A i) (x y : M (e j)) :
    reindexSmul e M a (x + y) = reindexSmul e M a x + reindexSmul e M a y := sorry

/-- The reindexed homogeneous action sends zero to zero. -/
@[stacks 01CV "zero preservation under degree reindexing"]
theorem reindex_smul_zero (e : κprime →[ι] κ) (M : κ → Type y)
    [∀ j, AddMonoid (M j)] [Gmodule A M] {i : ι} {j : κprime} (a : A i) :
    reindexSmul e M a (0 : M (e j)) = 0 := sorry

/-- Addition of homogeneous scalars distributes over the reindexed action. -/
@[stacks 01CV "additivity in the scalar under degree reindexing"]
theorem reindex_add_smul (e : κprime →[ι] κ) (M : κ → Type y)
    [∀ j, AddMonoid (M j)] [Gmodule A M] {i : ι} {j : κprime}
    (a b : A i) (x : M (e j)) :
    reindexSmul e M (a + b) x = reindexSmul e M a x + reindexSmul e M b x := sorry

/-- The zero homogeneous scalar acts by zero after degree reindexing. -/
@[stacks 01CV "zero scalar law under degree reindexing"]
theorem reindex_zero_smul (e : κprime →[ι] κ) (M : κ → Type y)
    [∀ j, AddMonoid (M j)] [Gmodule A M] {i : ι} {j : κprime}
    (x : M (e j)) : reindexSmul e M (0 : A i) x = 0 := sorry

/-- 01CV: reindexing a graded module along an equivariant map of degree types. -/
@[reducible, stacks 01CV]
def reindex (e : κprime →[ι] κ) (M : κ → Type y) [∀ j, AddMonoid (M j)] [Gmodule A M] :
    Gmodule A (fun j => M (e j)) where
  smul := reindexSmul e M
  one_smul := reindex_one_smul e M
  mul_smul := reindex_mul_smul e M
  smul_add := reindex_smul_add e M
  smul_zero := reindex_smul_zero e M
  add_smul := reindex_add_smul e M
  zero_smul := reindex_zero_smul e M

/-- The reindexed homogeneous action is the original action transported along `e.map_vadd`. -/
theorem reindex_smul (e : κprime →[ι] κ) (M : κ → Type y) [∀ j, AddMonoid (M j)] [Gmodule A M]
    {i : ι} {j : κprime} (a : A i) (x : M (e j)) :
    @GradedMonoid.GSMul.smul ι κprime A (fun j => M (e j)) _
        (reindex e M).toGdistribMulAction.toGMulAction.toGSMul i j a x =
      Eq.mp (congrArg M (e.map_vadd i j).symm)
        (@GradedMonoid.GSMul.smul ι κ A M _ _ i (e j) a x) := sorry

/-- Transporting the reindexed action back along `e.map_vadd` recovers the original action. -/
theorem reindex_smul_cast (e : κprime →[ι] κ) (M : κ → Type y) [∀ j, AddMonoid (M j)] [Gmodule A M]
    {i : ι} {j : κprime} (a : A i) (x : M (e j)) :
    Eq.mp (congrArg M (e.map_vadd i j))
        (@GradedMonoid.GSMul.smul ι κprime A (fun j => M (e j)) _
          (reindex e M).toGdistribMulAction.toGMulAction.toGSMul i j a x) =
      @GradedMonoid.GSMul.smul ι κ A M _ _ i (e j) a x := sorry

/-- The homogeneous action transported across additive equivalences of all module pieces. -/
@[reducible, stacks 01CV "homogeneous action transported across additive equivalences"]
def ofAddEquivSmul (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    {i : ι} {j : κ} (a : A i) (x : N j) : N (i +ᵥ j) :=
  e (i +ᵥ j) (@GradedMonoid.GSMul.smul ι κ A M _ _ i j a ((e j).symm x))

/-- The induced scalar operation on the sigma type of transported homogeneous pieces. -/
@[reducible, stacks 01CV "total homogeneous action transported across additive equivalences"]
def ofAddEquivTotalSmul (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    (a : GradedMonoid A) (x : GradedMonoid N) : GradedMonoid N :=
  ⟨a.1 +ᵥ x.1, ofAddEquivSmul e a.2 x.2⟩

/-- The degree-zero unit is neutral for the transported homogeneous action. -/
@[stacks 01CV "unit law for transport across additive equivalences"]
theorem ofAddEquiv_one_smul (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    (x : GradedMonoid N) :
    ofAddEquivTotalSmul e (1 : GradedMonoid A) x = x := sorry

/-- Multiplication of homogeneous scalars is associative with the transported action. -/
@[stacks 01CV "multiplication law for transport across additive equivalences"]
theorem ofAddEquiv_mul_smul (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    (a b : GradedMonoid A) (x : GradedMonoid N) :
    ofAddEquivTotalSmul e (a * b) x =
      ofAddEquivTotalSmul e a (ofAddEquivTotalSmul e b x) := sorry

/-- The transported homogeneous action distributes over addition in a target piece. -/
@[stacks 01CV "additivity in a transported module piece"]
theorem ofAddEquiv_smul_add (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    {i : ι} {j : κ} (a : A i) (x y : N j) :
    ofAddEquivSmul e a (x + y) = ofAddEquivSmul e a x + ofAddEquivSmul e a y := sorry

/-- The transported homogeneous action sends zero to zero. -/
@[stacks 01CV "zero preservation under transport across additive equivalences"]
theorem ofAddEquiv_smul_zero (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    {i : ι} {j : κ} (a : A i) : ofAddEquivSmul e a (0 : N j) = 0 := sorry

/-- Addition of homogeneous scalars distributes over the transported action. -/
@[stacks 01CV "additivity in the scalar after transport across additive equivalences"]
theorem ofAddEquiv_add_smul (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    {i : ι} {j : κ} (a b : A i) (x : N j) :
    ofAddEquivSmul e (a + b) x = ofAddEquivSmul e a x + ofAddEquivSmul e b x := sorry

/-- The zero homogeneous scalar acts by zero after transport across additive equivalences. -/
@[stacks 01CV "zero scalar law after transport across additive equivalences"]
theorem ofAddEquiv_zero_smul (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    {i : ι} {j : κ} (x : N j) : ofAddEquivSmul e (0 : A i) x = 0 := sorry

/-- 01CV: transporting a graded module structure across additive equivalences of its pieces. -/
@[reducible, stacks 01CV]
def ofAddEquiv (e : ∀ j, M j ≃+ N j) [Gmodule A M] : Gmodule A N where
  smul := ofAddEquivSmul e
  one_smul := ofAddEquiv_one_smul e
  mul_smul := ofAddEquiv_mul_smul e
  smul_add := ofAddEquiv_smul_add e
  smul_zero := ofAddEquiv_smul_zero e
  add_smul := ofAddEquiv_add_smul e
  zero_smul := ofAddEquiv_zero_smul e

/-- The transported homogeneous action is computed by conjugating the original action by `e`. -/
theorem ofAddEquiv_smul (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    {i : ι} {j : κ} (a : A i) (x : N j) :
    @GradedMonoid.GSMul.smul ι κ A N _
        (ofAddEquiv e).toGdistribMulAction.toGMulAction.toGSMul i j a x =
      e (i +ᵥ j) (@GradedMonoid.GSMul.smul ι κ A M _ _ i j a ((e j).symm x)) := sorry

/-- Applying the inverse target equivalence to the transported action recovers the old action. -/
theorem ofAddEquiv_smul_symm (e : ∀ j, M j ≃+ N j) [Gmodule A M]
    {i : ι} {j : κ} (a : A i) (x : N j) :
    (e (i +ᵥ j)).symm
        (@GradedMonoid.GSMul.smul ι κ A N _
          (ofAddEquiv e).toGdistribMulAction.toGMulAction.toGSMul i j a x) =
      @GradedMonoid.GSMul.smul ι κ A M _ _ i j a ((e j).symm x) := sorry

end DirectSum.Gmodule
